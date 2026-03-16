#!/usr/bin/env python3
"""
golf_picks.py — One-and-Done PGA Tour Picks Advisor

Helps you dominate a one-and-done pool by scoring every player in this
week's field across win probability, course fit, future value, and purse size.

Usage:
  python golf_picks.py                          # Get this week's top 10 picks
  python golf_picks.py --used "Rory McIlroy"   # Mark a player as used this season
  python golf_picks.py --show-used              # See all players used this season
  python golf_picks.py --reset                  # Reset used list (new season)
  python golf_picks.py --refresh                # Force-refresh all cached data
  python golf_picks.py --config                 # Set/update your DataGolf API key

Data sources:
  • DataGolf API  — field, rankings, SG stats, win probabilities, schedule
  • ESPN Golf API — fallback tournament info, supplementary field data
"""

import argparse
import difflib
import json
import math
import os
import re
import sys
import threading
import time
import webbrowser
from datetime import date, datetime, timedelta
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from typing import Optional
from urllib.parse import urlparse

try:
    import requests
except ImportError:
    print("Missing dependency. Run:  pip install requests")
    sys.exit(1)

# ══════════════════════════════════════════════════════════════════════════════
# PATHS & CONSTANTS
# ══════════════════════════════════════════════════════════════════════════════

BASE_DIR          = Path(__file__).parent
DATA_DIR          = BASE_DIR / "golf_data"
CACHE_DIR         = DATA_DIR / "cache"
USED_FILE         = DATA_DIR / "used_players.json"
CFG_FILE          = DATA_DIR / "config.json"
PICK_HISTORY_FILE  = DATA_DIR / "pick_history.json"
UI_HTML            = BASE_DIR / "golf_picks_ui.html"
STATIC_HTML_OUTPUT = BASE_DIR / "golf_picks.html"
UI_PORT            = 5051
MPSP_BASE          = "https://mpsp.protourfantasygolf.com"

DATA_DIR.mkdir(exist_ok=True)
CACHE_DIR.mkdir(exist_ok=True)

DG_BASE   = "https://feeds.datagolf.com"
ESPN_BASE = "https://site.api.espn.com/apis/site/v2/sports/golf"

# Scoring weights — must sum to 1.0
WEIGHTS = {
    "win_top10":    0.40,   # Win prob + top-10 probability this week
    "course_fit":   0.25,   # SG profile vs course demands + history bonus
    "future_value": 0.25,   # Expected future earnings × event-tier fit
    "purse_size":   0.10,   # How valuable is this week's purse
}

# Per-mode weights for the web UI (7 components)
MODE_WEIGHTS = {
    "conservative": {
        "win_top10": 0.32, "course_fit": 0.25, "future_value": 0.22,
        "purse_size": 0.10, "league_advantage": 0.05, "pick_leverage": 0.04,
        "leader_exclusivity": 0.02,
    },
    "balanced": {
        "win_top10": 0.30, "course_fit": 0.18, "future_value": 0.18,
        "purse_size": 0.08, "league_advantage": 0.10, "pick_leverage": 0.10,
        "leader_exclusivity": 0.06,
    },
    "chase": {
        "win_top10": 0.25, "course_fit": 0.12, "future_value": 0.12,
        "purse_size": 0.05, "league_advantage": 0.14, "pick_leverage": 0.18,
        "leader_exclusivity": 0.14,
    },
}

# Commissioner's Cup event keywords
CUP_KEYWORDS = [
    "masters", "u.s. open", "open championship", "pga championship",
    "the players", "genesis", "arnold palmer", "memorial tournament",
    "bmw championship", "tour championship", "rbc canadian", "fedex st. jude",
    "travelers", "wells fargo", "scottish open", "zurich classic",
]

# Cache TTLs (seconds)
CACHE_TTL = {
    "field":         6 * 3600,
    "rankings":     12 * 3600,
    "predictions":   6 * 3600,
    "schedule":     24 * 3600,
    "history":       7 * 24 * 3600,
}

# Purse thresholds
HIGH_VALUE_PURSE  = 15_000_000
ELEVATED_PURSE    = 10_000_000
ELITE_RANK_CUTOFF = 20          # OWGR top-20 = elite

MAJOR_KEYWORDS    = ["masters", "u.s. open", "open championship", "pga championship"]
ELEVATED_KEYWORDS = MAJOR_KEYWORDS + [
    "the players", "genesis", "arnold palmer", "memorial", "bmw championship",
    "tour championship", "travelers", "wells fargo", "scottish open",
    "fedex st. jude", "rbc canadian", "zurich classic",
]

# ══════════════════════════════════════════════════════════════════════════════
# SG FOCUS PRESETS  (use --focus <name> to override course profile)
# ══════════════════════════════════════════════════════════════════════════════

SG_FOCUS_PRESETS = {
    "driving":  {"sg_ott": 0.55, "sg_app": 0.25, "sg_arg": 0.10, "sg_putt": 0.10, "type": "driving"},
    "approach": {"sg_ott": 0.10, "sg_app": 0.55, "sg_arg": 0.15, "sg_putt": 0.20, "type": "approach"},
    "putting":  {"sg_ott": 0.10, "sg_app": 0.20, "sg_arg": 0.20, "sg_putt": 0.50, "type": "putting"},
    "arg":      {"sg_ott": 0.10, "sg_app": 0.25, "sg_arg": 0.45, "sg_putt": 0.20, "type": "arg"},
    "balanced": {"sg_ott": 0.25, "sg_app": 0.35, "sg_arg": 0.15, "sg_putt": 0.25, "type": "balanced"},
    "ballstriking": {"sg_ott": 0.35, "sg_app": 0.45, "sg_arg": 0.10, "sg_putt": 0.10, "type": "ballstriking"},
}

# ══════════════════════════════════════════════════════════════════════════════
# COURSE PROFILE DATABASE
# weights: how much each SG category matters on this course
# ══════════════════════════════════════════════════════════════════════════════

COURSE_PROFILES = {
    "augusta national":    {"sg_ott": 0.10, "sg_app": 0.45, "sg_arg": 0.15, "sg_putt": 0.30, "type": "approach/putting"},
    "pebble beach":        {"sg_ott": 0.30, "sg_app": 0.35, "sg_arg": 0.10, "sg_putt": 0.25, "type": "driving/approach"},
    "riviera":             {"sg_ott": 0.20, "sg_app": 0.40, "sg_arg": 0.10, "sg_putt": 0.30, "type": "approach/putting"},
    "torrey pines":        {"sg_ott": 0.35, "sg_app": 0.35, "sg_arg": 0.10, "sg_putt": 0.20, "type": "driving/approach"},
    "bay hill":            {"sg_ott": 0.30, "sg_app": 0.40, "sg_arg": 0.10, "sg_putt": 0.20, "type": "approach"},
    "muirfield village":   {"sg_ott": 0.10, "sg_app": 0.45, "sg_arg": 0.20, "sg_putt": 0.25, "type": "approach"},
    "tpc sawgrass":        {"sg_ott": 0.10, "sg_app": 0.35, "sg_arg": 0.20, "sg_putt": 0.35, "type": "approach/putting"},
    "bethpage":            {"sg_ott": 0.30, "sg_app": 0.40, "sg_arg": 0.10, "sg_putt": 0.20, "type": "driving/approach"},
    "quail hollow":        {"sg_ott": 0.30, "sg_app": 0.40, "sg_arg": 0.15, "sg_putt": 0.15, "type": "driving/approach"},
    "harbour town":        {"sg_ott": 0.10, "sg_app": 0.30, "sg_arg": 0.25, "sg_putt": 0.35, "type": "putting/arg"},
    "tpc scottsdale":      {"sg_ott": 0.10, "sg_app": 0.30, "sg_arg": 0.25, "sg_putt": 0.35, "type": "putting"},
    "kapalua":             {"sg_ott": 0.40, "sg_app": 0.30, "sg_arg": 0.10, "sg_putt": 0.20, "type": "driving"},
    "east lake":           {"sg_ott": 0.15, "sg_app": 0.40, "sg_arg": 0.15, "sg_putt": 0.30, "type": "approach"},
    "aronimink":           {"sg_ott": 0.15, "sg_app": 0.45, "sg_arg": 0.15, "sg_putt": 0.25, "type": "approach"},
    "colonial":            {"sg_ott": 0.10, "sg_app": 0.35, "sg_arg": 0.25, "sg_putt": 0.30, "type": "approach/arg"},
    "congaree":            {"sg_ott": 0.30, "sg_app": 0.35, "sg_arg": 0.10, "sg_putt": 0.25, "type": "driving/approach"},
    "detroit golf":        {"sg_ott": 0.20, "sg_app": 0.35, "sg_arg": 0.20, "sg_putt": 0.25, "type": "balanced"},
    "olympia fields":      {"sg_ott": 0.25, "sg_app": 0.40, "sg_arg": 0.10, "sg_putt": 0.25, "type": "approach"},
    "shadow creek":        {"sg_ott": 0.15, "sg_app": 0.40, "sg_arg": 0.15, "sg_putt": 0.30, "type": "approach"},
    "tpc twin cities":     {"sg_ott": 0.20, "sg_app": 0.30, "sg_arg": 0.20, "sg_putt": 0.30, "type": "putting"},
    "default":             {"sg_ott": 0.25, "sg_app": 0.35, "sg_arg": 0.15, "sg_putt": 0.25, "type": "balanced"},
}

# ══════════════════════════════════════════════════════════════════════════════
# CONFIG
# ══════════════════════════════════════════════════════════════════════════════

def load_cfg() -> dict:
    return json.loads(CFG_FILE.read_text()) if CFG_FILE.exists() else {}

def save_cfg(cfg: dict):
    CFG_FILE.write_text(json.dumps(cfg, indent=2))

def get_api_key() -> str:
    cfg = load_cfg()
    key = cfg.get("datagolf_api_key", "").strip()
    if not key:
        print("\n  DataGolf API key not set.")
        print("  Free key available at: https://datagolf.com/api-access")
        key = input("  Enter your DataGolf API key: ").strip()
        if key:
            cfg["datagolf_api_key"] = key
            save_cfg(cfg)
            print("  Key saved to golf_data/config.json\n")
        else:
            print("  WARNING: No key provided. Data may be limited.\n")
    return key

def cmd_config():
    cfg = load_cfg()
    cur = cfg.get("datagolf_api_key", "")
    display = f"...{cur[-8:]}" if len(cur) > 8 else "(not set)"
    print(f"\n  Current DataGolf API key: {display}")
    print("  Get a free key at: https://datagolf.com/api-access")
    new_key = input("  New API key (Enter to keep current): ").strip()
    if new_key:
        cfg["datagolf_api_key"] = new_key
        save_cfg(cfg)
        print("  API key updated.")

# ══════════════════════════════════════════════════════════════════════════════
# CACHE
# ══════════════════════════════════════════════════════════════════════════════

def _cp(name: str) -> Path:
    return CACHE_DIR / f"{name}.json"

def cache_read(name: str, ttl: int) -> Optional[dict]:
    p = _cp(name)
    if not p.exists():
        return None
    try:
        data = json.loads(p.read_text())
        if time.time() - data.get("_at", 0) <= ttl:
            return data["payload"]
    except Exception:
        pass
    return None

def cache_write(name: str, payload):
    _cp(name).write_text(json.dumps({"_at": time.time(), "payload": payload}, indent=2))

def clear_cache():
    for f in CACHE_DIR.glob("*.json"):
        f.unlink()
    print("  Cache cleared.")

# ══════════════════════════════════════════════════════════════════════════════
# HTTP HELPERS
# ══════════════════════════════════════════════════════════════════════════════

def _post(url: str, payload: dict, headers: dict = None, timeout: int = 15) -> Optional[dict]:
    try:
        r = requests.post(url, json=payload, timeout=timeout,
                          headers={"User-Agent": "golf-picks-advisor/1.0", **(headers or {})})
        r.raise_for_status()
        return r.json()
    except Exception:
        return None

def _get(url: str, params: dict = None, timeout: int = 15) -> Optional[dict]:
    try:
        r = requests.get(url, params=params or {}, timeout=timeout,
                         headers={"User-Agent": "golf-picks-advisor/1.0"})
        r.raise_for_status()
        return r.json()
    except requests.exceptions.HTTPError as e:
        print(f"    [WARN] HTTP {e.response.status_code} from {url}")
        return None
    except requests.exceptions.RequestException as e:
        print(f"    [WARN] Request failed: {e}")
        return None

def dg_get(endpoint: str, params: dict, api_key: str,
           cache_name: str, ttl: int) -> Optional[dict]:
    """DataGolf API call with caching + stale fallback."""
    if ttl > 0:
        cached = cache_read(cache_name, ttl)
        if cached is not None:
            return cached
    params = {**params, "key": api_key, "file_format": "json"}
    data = _get(f"{DG_BASE}/{endpoint}", params)
    if data:
        cache_write(cache_name, data)
        return data
    # Try stale cache
    stale = cache_read(cache_name, ttl=99_999_999)
    if stale:
        print("    [INFO] Using stale cached data.")
    return stale

# ══════════════════════════════════════════════════════════════════════════════
# DATA FETCHERS — DATAGOLF
# ══════════════════════════════════════════════════════════════════════════════

def _val_tier(purse: float, is_major: bool, is_elev: bool) -> int:
    if is_major:              return 5
    if purse >= HIGH_VALUE_PURSE: return 4
    if is_elev or purse >= ELEVATED_PURSE: return 3
    if purse >= 7_000_000:   return 2
    return 1

def fetch_pgatour_purses() -> dict:
    """Fetch purse amounts from PGA Tour GraphQL API. Returns {tournament_name: purse_float}."""
    cached = cache_read("pgatour_purses", CACHE_TTL["schedule"])
    if cached is not None:
        return cached
    query = """{ schedule(tourCode: "R", year: "2026") {
        upcoming { tournaments { tournamentName purse startDate } }
        completed { tournaments { tournamentName purse startDate } }
    } }"""
    data = _post(
        "https://orchestrator.pgatour.com/graphql",
        {"query": query},
        headers={"x-api-key": "da2-gsrx5bibzbb4njvhl7t6jgw4vc", "Content-Type": "application/json"},
    )
    result = {}
    if not data or not data.get("data"):
        return result
    schedule = data["data"].get("schedule", {})
    for section in ("upcoming", "completed"):
        for month in schedule.get(section, []):
            for t in month.get("tournaments", []):
                name = t.get("tournamentName", "")
                purse_str = t.get("purse") or ""
                try:
                    purse = float(purse_str.replace("$", "").replace(",", ""))
                except (ValueError, AttributeError):
                    purse = 0.0
                if name and purse > 0:
                    result[name] = purse
    cache_write("pgatour_purses", result)
    return result

def fetch_schedule(api_key: str) -> list[dict]:
    data = dg_get("get-schedule", {"tour": "pga"}, api_key,
                  "schedule", CACHE_TTL["schedule"])
    if not data:
        return []
    pgatour_purses = fetch_pgatour_purses()
    events = data if isinstance(data, list) else data.get("schedule", [])
    out = []
    for ev in events:
        name = str(ev.get("event_name", ""))
        nl   = name.lower()
        purse = float(ev.get("purse", 0) or 0)
        if purse == 0 and name in pgatour_purses:
            purse = pgatour_purses[name]
        is_major = any(k in nl for k in MAJOR_KEYWORDS)
        is_elev  = any(k in nl for k in ELEVATED_KEYWORDS)
        out.append({
            "event_id":   ev.get("event_id") or ev.get("calendar_year_event_id"),
            "event_name": name,
            "course":     str(ev.get("course", "")),
            "start_date": str(ev.get("start_date", "")),
            "end_date":   str(ev.get("end_date", "")),
            "purse":      purse,
            "is_major":   is_major,
            "is_elevated": is_elev or is_major or purse >= ELEVATED_PURSE,
            "value_tier": _val_tier(purse, is_major, is_elev),
        })
    return out

def fetch_field(api_key: str) -> list[dict]:
    data = dg_get("field-updates", {"tour": "pga"}, api_key,
                  "field", CACHE_TTL["field"])
    if not data:
        return []
    raw = data if isinstance(data, list) else data.get("field", [])
    out = []
    for p in raw:
        dg_id = int(p.get("dg_id") or p.get("datagolf_id") or 0)
        name  = str(p.get("player_name", "")).strip()
        if name:
            out.append({"dg_id": dg_id, "name": name})
    return out

def fetch_rankings(api_key: str) -> dict:
    """Returns {dg_id: {...stats...}}"""
    rank_data = dg_get("preds/get-dg-rankings", {}, api_key, "rankings", CACHE_TTL["rankings"])
    sg_data   = dg_get("preds/skill-ratings", {"display": "value"}, api_key, "skill_ratings", CACHE_TTL["rankings"])

    # Build SG lookup by dg_id
    sg_by_id = {}
    if sg_data:
        sg_rows = sg_data if isinstance(sg_data, list) else sg_data.get("players", [])
        for p in sg_rows:
            dg_id = int(p.get("dg_id") or 0)
            if dg_id:
                sg_by_id[dg_id] = p

    if not rank_data:
        return {}
    rows = rank_data if isinstance(rank_data, list) else rank_data.get("rankings", [])
    result = {}
    for p in rows:
        dg_id = int(p.get("dg_id") or p.get("datagolf_id") or 0)
        if not dg_id:
            continue
        sg = sg_by_id.get(dg_id, {})
        result[dg_id] = {
            "name":     str(p.get("player_name", "")),
            "dg_rank":  int(p.get("datagolf_rank") or 999),
            "owgr":     int(p.get("owgr_rank") or p.get("owgr") or 999),
            "sg_total": float(sg.get("sg_total") or 0),
            "sg_ott":   float(sg.get("sg_ott")   or 0),
            "sg_app":   float(sg.get("sg_app")   or 0),
            "sg_arg":   float(sg.get("sg_arg")   or 0),
            "sg_putt":  float(sg.get("sg_putt")  or 0),
        }
    return result

def fetch_predictions(api_key: str) -> dict:
    """Returns {dg_id: {win_prob, top10_prob, make_cut_prob, ...}}"""
    data = dg_get("preds/pre-tournament",
                  {"tour": "pga", "odds_format": "percent"},
                  api_key, "predictions", CACHE_TTL["predictions"])
    if not data:
        return {}
    # DataGolf may return baseline_history_fit, baseline, or a flat list
    rows = []
    if isinstance(data, dict):
        rows = (data.get("baseline_history_fit")
                or data.get("baseline")
                or data.get("data")
                or [])
    elif isinstance(data, list):
        rows = data
    result = {}
    for p in rows:
        dg_id = int(p.get("dg_id") or p.get("datagolf_id") or 0)
        if not dg_id:
            continue
        result[dg_id] = {
            "win_prob":      float(p.get("win")      or p.get("win_prob")  or 0),
            "top5_prob":     float(p.get("top_5")    or p.get("top5")      or 0),
            "top10_prob":    float(p.get("top_10")   or p.get("top10")     or 0),
            "top20_prob":    float(p.get("top_20")   or p.get("top20")     or 0),
            "make_cut_prob": float(p.get("make_cut") or p.get("mc")        or 70),
        }
    return result

def fetch_course_history(api_key: str, event_id, years: int = 5) -> dict:
    """Historical results at this event/course.  Returns {player_name: summary}."""
    if not event_id:
        return {}
    combined: dict[str, dict] = {}
    cur_year = datetime.now().year
    for yr in range(cur_year - 1, cur_year - 1 - years, -1):
        cname = f"history_{event_id}_{yr}"
        data = cache_read(cname, CACHE_TTL["history"])
        if data is None:
            data = dg_get("historical-raw-data/rounds",
                          {"tour": "pga", "event_id": event_id, "year": yr},
                          api_key, cname, ttl=0)
        if not data:
            continue
        rows = data if isinstance(data, list) else data.get("scores", data.get("data", data.get("rounds", [])))
        for r in rows:
            name = str(r.get("player_name", "")).strip()
            if not name:
                continue
            if name not in combined:
                combined[name] = {"results": [], "years": set()}
            combined[name]["years"].add(yr)
            fin_raw = str(r.get("fin_text") or r.get("finish") or "")
            combined[name]["results"].append({
                "year": yr,
                "finish_raw": fin_raw,
                "finish_num": _parse_finish(fin_raw),
            })
    # Summarise
    summary = {}
    for name, info in combined.items():
        nums = [r["finish_num"] for r in info["results"] if r["finish_num"] is not None]
        summary[name] = {
            "years_played": len(info["years"]),
            "made_cuts":    len(nums),
            "best_finish":  min(nums) if nums else None,
            "avg_finish":   round(sum(nums) / len(nums), 1) if nums else None,
            "top10_count":  sum(1 for f in nums if f <= 10),
            "recent":       sorted(info["results"], key=lambda x: x["year"], reverse=True)[:3],
        }
    return summary

def _parse_finish(s: str) -> Optional[int]:
    cleaned = s.upper().replace("T", "").strip()
    try:
        return int(cleaned)
    except ValueError:
        return None

# ══════════════════════════════════════════════════════════════════════════════
# DATA FETCHERS — ESPN (fallback / supplementary)
# ══════════════════════════════════════════════════════════════════════════════

def fetch_espn_current_tournament() -> Optional[dict]:
    data = _get(f"{ESPN_BASE}/pga/scoreboard")
    if not data:
        return None
    events = data.get("events", [])
    if not events:
        return None
    ev = events[0]
    comp = ev.get("competitions", [{}])[0]
    venue = comp.get("venue", {})
    return {
        "event_name": ev.get("name", ev.get("shortName", "")),
        "course":     venue.get("fullName", ""),
        "start_date": ev.get("date", "")[:10],
    }

def fetch_espn_field(espn_event_id: str) -> list[dict]:
    """Pull competitor names from ESPN scoreboard for field enrichment."""
    data = _get(f"{ESPN_BASE}/leaderboard", {"event": espn_event_id})
    if not data:
        return []
    names = []
    for comp in data.get("events", [{}])[0].get("competitions", [{}])[0].get("competitors", []):
        athlete = comp.get("athlete", {})
        name = athlete.get("displayName", "")
        if name:
            names.append(name)
    return [{"dg_id": 0, "name": n} for n in names]

# ══════════════════════════════════════════════════════════════════════════════
# TOURNAMENT DETECTION
# ══════════════════════════════════════════════════════════════════════════════

def detect_tournament(schedule: list[dict], api_key: str) -> Optional[dict]:
    today = date.today()
    # 1. Current week from schedule
    for ev in schedule:
        try:
            start = date.fromisoformat(ev["start_date"])
            raw_end = ev.get("end_date", "")
            end = date.fromisoformat(raw_end) if raw_end else start + timedelta(days=3)
            if start <= today <= end:
                return ev
        except (ValueError, TypeError):
            continue
    # 2. Next upcoming
    upcoming = []
    for ev in schedule:
        try:
            start = date.fromisoformat(ev["start_date"])
            if start > today:
                upcoming.append((start, ev))
        except (ValueError, TypeError):
            continue
    if upcoming:
        upcoming.sort(key=lambda x: x[0])
        return upcoming[0][1]
    # 3. ESPN fallback
    espn = fetch_espn_current_tournament()
    if espn:
        espn.setdefault("purse", 8_000_000)
        espn.setdefault("value_tier", 2)
        espn.setdefault("is_major", False)
        espn.setdefault("is_elevated", False)
        espn.setdefault("event_id", None)
        return espn
    return None

def remaining_schedule(schedule: list[dict], current_name: str) -> list[dict]:
    today = date.today()
    out = []
    for ev in schedule:
        try:
            start = date.fromisoformat(ev["start_date"])
            if start > today and ev.get("event_name", "") != current_name:
                out.append(ev)
        except (ValueError, TypeError):
            continue
    return out

# ══════════════════════════════════════════════════════════════════════════════
# USED PLAYERS
# ══════════════════════════════════════════════════════════════════════════════

def load_used() -> dict:
    if USED_FILE.exists():
        try:
            return json.loads(USED_FILE.read_text())
        except Exception:
            pass
    return {"season": str(date.today().year), "players": []}

def save_used(data: dict):
    USED_FILE.write_text(json.dumps(data, indent=2))

def cmd_mark_used(player_name: str):
    used = load_used()
    existing = [p["name"] for p in used["players"]]
    matches = difflib.get_close_matches(player_name, existing, n=1, cutoff=0.75)
    if matches:
        print(f"  Matched '{player_name}' → '{matches[0]}' (already in list).")
        return
    # Check case-insensitive exact match
    if any(p["name"].lower() == player_name.lower() for p in used["players"]):
        print(f"  '{player_name}' is already marked as used.")
        return
    used["players"].append({"name": player_name, "date": str(date.today())})
    save_used(used)
    print(f"  ✓ '{player_name}' added to used players list.")

def cmd_show_used():
    used = load_used()
    if not used["players"]:
        print(f"\n  No players used yet this season ({used.get('season')}).")
        return
    print(f"\n  ── Used Players  ({used.get('season')} season) ──")
    for i, p in enumerate(sorted(used["players"], key=lambda x: x["date"]), 1):
        print(f"  {i:2}. {p['name']:<32}  used: {p['date']}")
    print(f"\n  Total: {len(used['players'])}")

def cmd_reset():
    yn = input("  Reset ALL used players for this season? [y/N]: ").strip().lower()
    if yn == "y":
        save_used({"season": str(date.today().year), "players": []})
        print("  Used players list reset.")
    else:
        print("  Aborted.")

def _normalize_name(name: str) -> str:
    """Normalize 'Last, First' and 'First Last' to the same canonical form."""
    name = name.strip().lower()
    if "," in name:
        last, first = name.split(",", 1)
        return f"{first.strip()} {last.strip()}"
    return name

def used_names_set(used: dict) -> set:
    return {_normalize_name(p["name"]) for p in used.get("players", [])}

# ══════════════════════════════════════════════════════════════════════════════
# SCORING COMPONENTS
# ══════════════════════════════════════════════════════════════════════════════

def _course_profile(course_name: str) -> dict:
    cl = course_name.lower()
    for key, profile in COURSE_PROFILES.items():
        if key == "default":
            continue
        if key in cl or cl in key:
            return profile
    # Fuzzy match
    keys = [k for k in COURSE_PROFILES if k != "default"]
    matches = difflib.get_close_matches(cl, keys, n=1, cutoff=0.5)
    if matches:
        return COURSE_PROFILES[matches[0]]
    return COURSE_PROFILES["default"]

def _sg_course_fit(stats: dict, profile: dict) -> float:
    return (stats.get("sg_ott",  0) * profile["sg_ott"]  +
            stats.get("sg_app",  0) * profile["sg_app"]  +
            stats.get("sg_arg",  0) * profile["sg_arg"]  +
            stats.get("sg_putt", 0) * profile["sg_putt"])

def _rank_contention_prob(rank: int) -> float:
    """Rough win-probability proxy for a generic elite event by world ranking."""
    if rank <= 3:   return 0.12
    if rank <= 5:   return 0.09
    if rank <= 10:  return 0.06
    if rank <= 20:  return 0.035
    if rank <= 30:  return 0.022
    if rank <= 50:  return 0.015
    if rank <= 75:  return 0.008
    if rank <= 100: return 0.005
    return 0.001

def best_future_spots(stats: dict, rem: list[dict], n: int = 3) -> list[dict]:
    """
    Return the top N upcoming elite events where this player's SG profile
    best matches the course demands, weighted by event tier/purse.
    """
    results = []
    for ev in rem:
        if ev.get("value_tier", 1) < 3:
            continue
        course  = ev.get("course", "")
        profile = _course_profile(course)
        sg_fit  = _sg_course_fit(stats, profile)
        tier    = ev.get("value_tier", 1)
        purse   = ev.get("purse", 0)
        tier_mult = {5: 2.0, 4: 1.5, 3: 1.0}.get(tier, 1.0)
        combined = sg_fit * tier_mult
        results.append({
            "event_name": ev["event_name"],
            "start_date": ev["start_date"],
            "purse":      purse,
            "tier":       tier,
            "is_major":   ev.get("is_major", False),
            "sg_fit":     round(sg_fit, 3),
            "combined":   round(combined, 3),
            "profile_type": profile.get("type", "balanced"),
        })
    results.sort(key=lambda x: x["combined"], reverse=True)
    return results[:n]

def future_value_score(stats: dict, rem: list[dict], cur_tier: int) -> float:
    """
    Expected future earnings from remaining elite events, scaled by how
    well the current event tier justifies using this player now.
    """
    rank = min(stats.get("owgr", 999), stats.get("dg_rank", 999))
    p    = _rank_contention_prob(rank)
    ev_sum = 0.0
    for ev in rem:
        t = ev.get("value_tier", 1)
        if t < 3:
            continue  # Only count elevated+ events
        winner_share = float(ev.get("purse", 0)) * 0.18
        tier_mult = {5: 3.0, 4: 2.0, 3: 1.5}.get(t, 1.0)
        ev_sum += p * winner_share * tier_mult
    # Scale by how good this week is — good week = more reason to use now
    cur_mult = {5: 1.5, 4: 1.2, 3: 1.0, 2: 0.80, 1: 0.60}.get(cur_tier, 0.80)
    return ev_sum * cur_mult

def _normalize(vals: list[float], lo: float = 0.0, hi: float = 100.0) -> list[float]:
    mn, mx = min(vals), max(vals)
    if mx == mn:
        return [50.0] * len(vals)
    return [lo + (hi - lo) * (v - mn) / (mx - mn) for v in vals]

def _history_bonus(name: str, course_history: dict) -> tuple[float, str]:
    """Return (bonus, summary_string) for a player based on course history."""
    for hname, info in course_history.items():
        if difflib.SequenceMatcher(None, name.lower(), hname.lower()).ratio() > 0.80:
            bf  = info.get("best_finish")
            af  = info.get("avg_finish")
            yp  = info.get("years_played", 0)
            t10 = info.get("top10_count", 0)
            mc  = info.get("made_cuts", 0)
            bonus = 0.0
            if bf is not None:
                if bf <= 3:   bonus = 1.5
                elif bf <= 10: bonus = 0.9
                elif bf <= 25: bonus = 0.3
            bf_str = f"best T{bf}" if bf else "no top finish"
            af_str = f"avg T{int(af)}" if af else ""
            parts  = [f"{yp} starts", bf_str]
            if af_str:  parts.append(af_str)
            if t10:     parts.append(f"{t10} top-10s")
            parts.append(f"{mc}/{yp} cuts")
            return bonus, ", ".join(parts)
    return 0.0, "No course history found"

# ══════════════════════════════════════════════════════════════════════════════
# MAIN SCORING ENGINE
# ══════════════════════════════════════════════════════════════════════════════

def score_field(
    field:          list[dict],
    rankings:       dict,
    predictions:    dict,
    tournament:     dict,
    rem_schedule:   list[dict],
    course_history: dict,
    used_lower:     set,
    sg_override:    dict = None,
) -> list[dict]:

    course  = tournament.get("course", "")
    purse   = float(tournament.get("purse", 0))
    cur_tier = int(tournament.get("value_tier", 2))
    profile = sg_override if sg_override else _course_profile(course)

    all_purses   = [float(e.get("purse", 0)) for e in rem_schedule] + [purse]
    max_purse    = max(all_purses) if all_purses else 1
    max_purse    = max_purse or 1
    purse_norm   = purse / max_purse  # same for every player this week

    candidates = []

    for pl in field:
        dg_id = pl["dg_id"]
        name  = pl["name"]

        # Skip used players (exact + fuzzy)
        norm_name = _normalize_name(name)
        if norm_name in used_lower:
            continue
        if any(difflib.SequenceMatcher(None, norm_name, u).ratio() > 0.85
               for u in used_lower):
            continue

        stats = rankings.get(dg_id, {})
        preds = predictions.get(dg_id, {})

        # Need at least some data
        if not stats and not preds:
            continue

        if stats.get("name"):
            name = stats["name"]

        owgr    = int(stats.get("owgr",    999))
        dg_rank = int(stats.get("dg_rank", 999))

        win_prob  = float(preds.get("win_prob",      0.5))
        top10_prob = float(preds.get("top10_prob",   5.0))
        cut_prob  = float(preds.get("make_cut_prob", 65.0))

        # ── Component raw scores ─────────────────────────────────────────────
        # 1. Win + top-10 (weight 3:1 within component)
        wt_raw = win_prob * 3.0 + top10_prob

        # 2. Course fit + history bonus
        cf_base     = _sg_course_fit(stats, profile)
        hist_bonus, hist_summary = _history_bonus(name, course_history)
        cf_raw = cf_base + hist_bonus

        # 3. Future value (per player, rank-based)
        fv_raw = future_value_score(stats, rem_schedule, cur_tier)

        # 4. Purse (same for everyone)
        ps_raw = purse_norm

        is_elite = owgr <= ELITE_RANK_CUTOFF

        candidates.append({
            "dg_id":         dg_id,
            "name":          name,
            "owgr":          owgr,
            "dg_rank":       dg_rank,
            "sg_total":      float(stats.get("sg_total", 0)),
            "sg_ott":        float(stats.get("sg_ott",   0)),
            "sg_app":        float(stats.get("sg_app",   0)),
            "sg_arg":        float(stats.get("sg_arg",   0)),
            "sg_putt":       float(stats.get("sg_putt",  0)),
            "win_prob":      win_prob,
            "top10_prob":    top10_prob,
            "make_cut_prob": cut_prob,
            "course_history": hist_summary,
            "is_elite":      is_elite,
            "_wt_raw":  wt_raw,
            "_cf_raw":  cf_raw,
            "_fv_raw":  fv_raw,
            "_ps_raw":  ps_raw,
            "future_spots": best_future_spots(stats, rem_schedule),
        })

    if not candidates:
        return []

    # ── Normalize each component across the field ────────────────────────────
    n = len(candidates)

    wt_n = _normalize([c["_wt_raw"] for c in candidates])
    cf_n = _normalize([c["_cf_raw"] for c in candidates])
    fv_n = _normalize([c["_fv_raw"] for c in candidates])
    # Purse is a scalar — convert to 0-100 directly, same for all
    ps_val = purse_norm * 100

    # Future elite events still available
    elite_remaining = [e for e in rem_schedule if e.get("value_tier", 1) >= 4]

    for i, c in enumerate(candidates):
        wt = wt_n[i]
        cf = cf_n[i]
        fv = fv_n[i]
        ps = ps_val

        score = (WEIGHTS["win_top10"]    * wt +
                 WEIGHTS["course_fit"]   * cf +
                 WEIGHTS["future_value"] * fv +
                 WEIGHTS["purse_size"]   * ps)

        c["score_win_top10"]   = round(wt, 1)
        c["score_course_fit"]  = round(cf, 1)
        c["score_future_val"]  = round(fv, 1)
        c["score_purse"]       = round(ps, 1)
        c["final_score"]       = round(score, 1)

        # "Save for later" flag: elite player, significant future opportunity,
        # current event is not major/elevated
        c["save_for_later"] = (
            c["is_elite"] and
            fv_n[i] >= 65 and
            cur_tier < 3 and
            len(elite_remaining) >= 2
        )

    candidates.sort(key=lambda x: x["final_score"], reverse=True)
    return candidates

# ══════════════════════════════════════════════════════════════════════════════
# REASONING GENERATOR
# ══════════════════════════════════════════════════════════════════════════════

def _leading_sg(player: dict) -> tuple[str, float]:
    cats = [("off-the-tee", player["sg_ott"]),
            ("approach",    player["sg_app"]),
            ("around-green",player["sg_arg"]),
            ("putting",     player["sg_putt"])]
    return max(cats, key=lambda x: x[1])

def generate_reason(player: dict, tournament: dict, rem: list[dict]) -> str:
    last     = player["name"].split()[-1]
    win      = player["win_prob"]
    t10      = player["top10_prob"]
    owgr     = player["owgr"]
    dg_rank  = player["dg_rank"]
    fv       = player["score_future_val"]
    cf       = player["score_course_fit"]
    purse    = tournament.get("purse", 0)
    course   = tournament.get("course", "this course")
    cur_tier = tournament.get("value_tier", 2)
    is_major = tournament.get("is_major", False)
    elite_rem = [e for e in rem if e.get("value_tier", 1) >= 4]
    next_major = next((e for e in rem if e.get("is_major")), None)
    sg_cat, sg_val = _leading_sg(player)
    hist = player.get("course_history", "")
    has_history = "top-10" in hist.lower() or ("best t" in hist.lower() and "best t0" not in hist.lower())

    # ── Save-for-later override ───────────────────────────────────────────────
    if player.get("save_for_later"):
        n_elite  = len(elite_rem)
        next_big = elite_rem[0]["event_name"] if elite_rem else "an upcoming major"
        s1 = (f"Despite being a top-{owgr} player in the world, this ${purse/1e6:.0f}M event "
              f"doesn't justify burning {last} when {n_elite} elite events remain.")
        s2 = (f"Save him for {next_big} — that's where his upside is maximized "
              f"in a one-and-done format.")
        return f"{s1} {s2}"

    # ── Sentence 1: Course fit / form / history ───────────────────────────────
    if has_history:
        s1 = (f"{last} has proven he can win at {course} ({hist.split(',')[0]}), "
              f"and his SG {sg_cat} ({sg_val:+.2f}) remains one of the best in this field.")
    elif cf >= 80:
        s1 = (f"{last}'s SG profile is a strong match for {course} — "
              f"his {sg_cat} game ({sg_val:+.2f}) is exactly what this course rewards.")
    elif cf >= 60:
        s1 = (f"{last} fits this course reasonably well, with his best SG coming {sg_cat} "
              f"({sg_val:+.2f}), which {course} consistently rewards.")
    else:
        s1 = (f"{last} brings elite overall form to Bay Hill — "
              f"ranked #{owgr} in the world with SG total of {player['sg_total']:+.2f}.")

    # ── Sentence 2: Strategic / one-and-done context ─────────────────────────
    if is_major or cur_tier == 5:
        s2 = (f"This is a major — with a {win:.1f}% win probability and {t10:.1f}% top-10 chance, "
              f"there's no better week to spend {last}.")
    elif cur_tier >= 4 and next_major and fv >= 60:
        weeks_to_major = (date.fromisoformat(next_major["start_date"]) - date.today()).days // 7
        s2 = (f"The {next_major['event_name']} is {weeks_to_major} weeks away, but at ${purse/1e6:.0f}M "
              f"this event is premium enough to justify using a top-{owgr} player now.")
    elif fv < 35:
        s2 = (f"With fewer elite events remaining on his schedule, the opportunity cost of using "
              f"{last} now is low — he's unlikely to have a better spot than this.")
    elif t10 >= 30:
        s2 = (f"His {t10:.1f}% top-10 probability is one of the highest in the field, "
              f"making him a high-floor pick even in a one-and-done context.")
    elif owgr <= 10 and fv >= 60 and cur_tier >= 3:
        s2 = (f"As a top-10 world player at a premium event, {last} offers the rare combination "
              f"of win upside this week and justified use of an elite pick.")
    elif next_major:
        weeks_to_major = (date.fromisoformat(next_major["start_date"]) - date.today()).days // 7
        s2 = (f"The next major is {weeks_to_major} weeks out — "
              f"if you're not saving {last} for that, this ${purse/1e6:.0f}M field is a strong spot to deploy him.")
    else:
        s2 = (f"At #{owgr} in the world with a {t10:.1f}% top-10 probability, "
              f"{last} offers dependable upside for a week-{cur_tier} event in a one-and-done league.")

    return f"{s1} {s2}"

# ══════════════════════════════════════════════════════════════════════════════
# REPORT
# ══════════════════════════════════════════════════════════════════════════════

TIER_LABELS = {1: "Standard", 2: "Elevated", 3: "Elevated+", 4: "Premium", 5: "MAJOR"}

def _short_name(event_name: str) -> str:
    """Return a short tournament name for summary display."""
    replacements = [
        ("presented by Mastercard", ""), ("presented by Workday", ""),
        ("presented by", ""), ("Arnold Palmer Invitational", "Arnold Palmer Inv."),
        ("THE PLAYERS Championship", "THE PLAYERS"),
        ("Masters Tournament", "Masters"),
        ("PGA Championship", "PGA Champ."),
        ("U.S. Open", "U.S. Open"),
        ("The Open Championship", "The Open"),
        ("RBC Heritage", "RBC Heritage"),
        ("Truist Championship", "Truist Champ."),
        ("the Memorial Tournament", "The Memorial"),
    ]
    name = event_name
    for old, new in replacements:
        name = name.replace(old, new).strip()
    return name

def _print_summary(picks: list[dict], tournament: dict, rem: list[dict]):
    W    = 78
    DIV2 = "─" * W
    cur_tier  = tournament.get("value_tier", 2)
    cur_name  = _short_name(tournament.get("event_name", "This Week"))
    next_major = next((e for e in rem if e.get("is_major")), None)
    elite_rem  = [e for e in rem if e.get("value_tier", 1) >= 4]

    print(f"\n  WEEKLY SUMMARY")
    print(DIV2)

    # ── Top recommendation ────────────────────────────────────────────────────
    top = picks[0]
    top_last = top["name"].split(",")[0].title() if "," in top["name"] else top["name"].split()[-1]
    print(f"\n  TOP PICK:  {top['name']}  (score {top['final_score']:.1f})")
    sg_cat, sg_val = _leading_sg(top)
    top_t10 = top["top10_prob"]
    print(f"  {_wrap(f'{top_last} is the strongest available option this week — best course fit at {cur_name} with elite SG {sg_cat} ({sg_val:+.2f}) and a {top_t10:.1f}% top-10 probability.', 74, '  ')}")

    # ── Use now vs. save ──────────────────────────────────────────────────────
    use_now  = [p for p in picks if not p.get("save_for_later") and p["score_future_val"] < 70]
    save     = [p for p in picks if p.get("save_for_later") or p["score_future_val"] >= 70]

    if save:
        save_names = ", ".join(
            p["name"].split(",")[0].title() if "," in p["name"] else p["name"].split()[-1]
            for p in save[:4]
        )
        next_big = _short_name(elite_rem[0]["event_name"]) if elite_rem else "upcoming majors"
        print(f"\n  CONSIDER SAVING:  {save_names}")
        print(f"  {_wrap(f'These players carry high future value — strong fits at upcoming elite events. Unless this is your planned week for them, {next_big} (next elite event) may be a better deployment.', 74, '  ')}")

    if use_now:
        use_names = ", ".join(
            p["name"].split(",")[0].title() if "," in p["name"] else p["name"].split()[-1]
            for p in use_now[:4]
        )
        print(f"\n  GOOD TO USE NOW:  {use_names}")
        print(f"  {_wrap('These players have lower future value scores — fewer elite events remain where they are the best fit, making this a good week to deploy them.', 74, '  ')}")

    # ── Course fit standouts ──────────────────────────────────────────────────
    best_fit = sorted(picks, key=lambda x: x["score_course_fit"], reverse=True)[:3]
    fit_names = ", ".join(
        p["name"].split(",")[0].title() if "," in p["name"] else p["name"].split()[-1]
        for p in best_fit
    )
    print(f"\n  BEST COURSE FIT:  {fit_names}")
    profile = _course_profile(tournament.get("course", ""))
    fit_type = profile.get("type", "balanced")
    fit_desc = fit_type.replace("/", " & ").replace("-", " ")
    print(f"  {_wrap(f'These players have the strongest SG profiles for {cur_name}, a course that rewards {fit_desc}. Their strokes-gained numbers most closely match what this layout demands.', 74, '  ')}")

    # ── Value plays (lower-ranked but strong fit) ─────────────────────────────
    value = [p for p in picks if p["owgr"] > 20 and p["score_course_fit"] >= 70]
    if value:
        val_names = ", ".join(
            p["name"].split(",")[0].title() if "," in p["name"] else p["name"].split()[-1]
            for p in value[:3]
        )
        print(f"\n  VALUE PLAYS:  {val_names}")
        print(f"  {_wrap('Lower-ranked players with a strong course fit this week. Good options if you are saving your elite picks for later in the season.', 74, '  ')}")

    # ── Major awareness ───────────────────────────────────────────────────────
    if next_major:
        weeks_away = (date.fromisoformat(next_major["start_date"]) - date.today()).days // 7
        major_name = _short_name(next_major["event_name"])
        print(f"\n  MAJOR ALERT:  {major_name} is {weeks_away} week(s) away")
        major_fits = sorted(
            [p for p in picks if p.get("future_spots") and
             any(_short_name(s["event_name"]) == major_name for s in p["future_spots"][:1])],
            key=lambda x: x["score_future_val"], reverse=True
        )[:3]
        if major_fits:
            major_names = ", ".join(
                p["name"].split(",")[0].title() if "," in p["name"] else p["name"].split()[-1]
                for p in major_fits
            )
            print(f"  {_wrap(f'{major_names} have {major_name} listed as their #1 future spot — consider saving them if you have other viable options this week.', 74, '  ')}")

def _wrap(text: str, width: int, indent: str) -> str:
    words, lines, line = text.split(), [], []
    for w in words:
        if sum(len(x) + 1 for x in line) + len(w) > width:
            lines.append(" ".join(line))
            line = [w]
        else:
            line.append(w)
    if line:
        lines.append(" ".join(line))
    return f"\n{indent}".join(lines)

def print_report(tournament: dict, picks: list[dict],
                 used_count: int, rem: list[dict], sg_profile: dict = None):
    W   = 78
    DIV = "═" * W
    DIV2= "─" * W

    print(f"\n{DIV}")
    print(f"  ⛳  ONE-AND-DONE PGA TOUR PICKS ADVISOR")
    print(f"  {datetime.now().strftime('%A, %B %d, %Y  %I:%M %p')}")
    print(DIV)

    name   = tournament.get("event_name", "Unknown")
    course = tournament.get("course", "Unknown")
    purse  = tournament.get("purse", 0)
    tier   = tournament.get("value_tier", 1)
    start  = tournament.get("start_date", "")
    end    = tournament.get("end_date", "")
    is_major = tournament.get("is_major", False)

    print(f"\n  THIS WEEK")
    print(f"  {'Tournament':<12}: {name}")
    print(f"  {'Course':<12}: {course}")
    print(f"  {'Dates':<12}: {start}  –  {end}")
    print(f"  {'Purse':<12}: ${purse:,.0f}")
    print(f"  {'Event Tier':<12}: {TIER_LABELS.get(tier, 'Standard')} (Tier {tier}/5)"
          + ("  ◄ MAJOR" if is_major else ""))
    print(f"  {'Used':<12}: {used_count} player(s) burned this season")

    if sg_profile:
        focus_type = sg_profile.get("type", "custom")
        ott  = sg_profile.get("sg_ott",  0)
        app  = sg_profile.get("sg_app",  0)
        arg  = sg_profile.get("sg_arg",  0)
        putt = sg_profile.get("sg_putt", 0)
        print(f"  {'SG Focus':<12}: {focus_type.upper()}  "
              f"(OTT {ott:.0%}  APP {app:.0%}  ARG {arg:.0%}  PUTT {putt:.0%})")

    elite_rem = [e for e in rem if e.get("value_tier", 1) >= 4]
    if elite_rem:
        print(f"\n  UPCOMING ELITE EVENTS  (consider saving top players for these)")
        for ev in elite_rem[:6]:
            tl   = "MAJOR" if ev.get("is_major") else f"Tier {ev['value_tier']}"
            p_m  = f"${ev.get('purse', 0)/1e6:.1f}M"
            print(f"    • {ev['event_name']:<42} {ev['start_date']}  {p_m:>7}  [{tl}]")

    print(f"\n{DIV}")
    print(f"  TOP 10 RECOMMENDED PICKS  (score = 0–100)")
    print(DIV)

    if not picks:
        print("\n  No eligible picks found. Check your API key, cache, or used-player list.")
        print(DIV + "\n")
        return

    # ── Quick-reference table ─────────────────────────────────────────────────
    print(f"\n  {'#':<4} {'Player':<26} {'Score':>6}  {'OWGR':>5}  {'Top10%':>6}  {'Best Future Spots'}")
    print(f"  {'-'*4} {'-'*26} {'-'*6}  {'-'*5}  {'-'*6}  {'-'*34}")
    for rank, p in enumerate(picks[:10], 1):
        elite = "★" if p["is_elite"] else " "
        name  = p["name"].title() if "," not in p["name"] else f"{p['name'].split(',')[1].strip()} {p['name'].split(',')[0].strip()}".title()
        spots = p.get("future_spots", [])
        spot_str = "  •  ".join(
            _short_name(s["event_name"]) for s in spots[:2]
        ) if spots else "—"
        print(f"  {rank:<4} {elite}{name:<25} {p['final_score']:>6.1f}  #{p['owgr']:<4}  {p['top10_prob']:>5.1f}%  {spot_str}")
    print()

    for rank, p in enumerate(picks[:10], 1):
        flag   = "  ⚠  SAVE FOR LATER" if p.get("save_for_later") else ""
        elite  = "★ " if p["is_elite"] else "  "
        print(f"\n  #{rank}  {elite}{p['name'].upper()}{flag}")
        print(DIV2)

        # Score bar
        bar_len = int(p["final_score"] / 2)
        bar     = "█" * bar_len + "░" * (50 - bar_len)
        print(f"  Score  {p['final_score']:5.1f}/100  [{bar}]")

        # Score breakdown
        print(f"  Components →  Win/Top10: {p['score_win_top10']:5.1f}  "
              f"Course Fit: {p['score_course_fit']:5.1f}  "
              f"Future Val: {p['score_future_val']:5.1f}  "
              f"Purse: {p['score_purse']:5.1f}")

        # Key metrics
        print(f"  OWGR #{p['owgr']:<5}  DG #{p['dg_rank']:<5}  "
              f"Win%: {p['win_prob']:5.1f}%   Top10%: {p['top10_prob']:5.1f}%   "
              f"CutMade%: {p['make_cut_prob']:4.0f}%")

        # SG stats
        print(f"  SG Total: {p['sg_total']:+.2f}   "
              f"OTT: {p['sg_ott']:+.2f}   "
              f"App: {p['sg_app']:+.2f}   "
              f"ARG: {p['sg_arg']:+.2f}   "
              f"Putt: {p['sg_putt']:+.2f}")

        # Course history
        print(f"  History : {p['course_history']}")

        # Best future spots
        spots = p.get("future_spots", [])
        if spots:
            parts = []
            for s in spots:
                label = s["event_name"]
                # Shorten common long names
                label = (label
                    .replace("presented by Mastercard", "")
                    .replace("presented by Workday", "")
                    .replace("presented by", "")
                    .strip())
                tag   = "MAJOR" if s["is_major"] else f"Tier {s['tier']}"
                month = s["start_date"][5:7]
                day   = s["start_date"][8:10]
                parts.append(f"{label} [{tag}] {month}/{day}")
            print(f"  Best For: {('  •  ').join(parts)}")

        # Reasoning
        reason = p.get("reason", "")
        if reason:
            wrapped = _wrap(reason, 70, "             ")
            print(f"  WHY NOW : {wrapped}")

    print(f"\n{DIV}")
    _print_summary(picks[:10], tournament, rem)
    print(f"{DIV}\n")

# ══════════════════════════════════════════════════════════════════════════════
# MONDAY AUTO-REFRESH
# ══════════════════════════════════════════════════════════════════════════════

def maybe_refresh_monday():
    """Clear cache on Mondays so every week opens with fresh data."""
    if date.today().weekday() != 0:      # 0 = Monday
        return
    cfg      = load_cfg()
    today_s  = str(date.today())
    if cfg.get("last_monday_refresh") == today_s:
        return                             # already refreshed today
    print("  → Monday detected — auto-clearing cache for fresh weekly data...")
    clear_cache()
    cfg["last_monday_refresh"] = today_s
    save_cfg(cfg)


# ══════════════════════════════════════════════════════════════════════════════
# STATIC HTML GENERATION  (python golf_picks.py --generate-html)
# ══════════════════════════════════════════════════════════════════════════════

def _build_static_player_data(
    field, rankings, predictions, tournament, rem_schedule,
    course_history, used_lower, sg_profile, pick_pcts, usage_rates,
) -> list:
    """
    Compute pre-normalized component scores for all eligible players.
    Returns player dicts with raw SG values + normalized scores so the
    browser can re-score with arbitrary weights and SG profiles client-side.
    """
    course   = tournament.get("course", "")
    purse    = float(tournament.get("purse", 0))
    cur_tier = int(tournament.get("value_tier", 2))
    profile  = sg_profile or _course_profile(course)

    all_purses = [float(e.get("purse", 0)) for e in rem_schedule] + [purse]
    ps_v = round(purse / (max(all_purses) or 1) * 100, 2)   # same for all

    pick_pcts   = pick_pcts   or {}
    usage_rates = usage_rates or {}

    raw = []
    for pl in field:
        dg_id = pl["dg_id"]
        name  = pl["name"]
        norm  = _normalize_name(name)
        if norm in used_lower:
            continue
        if any(difflib.SequenceMatcher(None, norm, u).ratio() > 0.85 for u in used_lower):
            continue
        stats = rankings.get(dg_id, {})
        preds = predictions.get(dg_id, {})
        if not stats and not preds:
            continue
        if stats.get("name"):
            name = stats["name"]

        owgr       = int(stats.get("owgr", 999))
        win_prob   = float(preds.get("win_prob",   0.5))
        top10_prob = float(preds.get("top10_prob", 5.0))

        hist_bonus, _ = _history_bonus(name, course_history)
        wt_raw = win_prob * 3.0 + top10_prob
        fv_raw = future_value_score(stats, rem_schedule, cur_tier)

        pct  = _fuzzy_lookup(name, pick_pcts)
        burn = _fuzzy_lookup(name, usage_rates)
        la_raw = max(0.0, 100.0 - burn) / 100.0
        pl_raw = max(0.0, 1.0 - pct / 33.0)
        le_raw = burn / 100.0

        is_elite = owgr <= ELITE_RANK_CUTOFF
        spots    = best_future_spots(stats, rem_schedule)
        save_ev  = ""
        if is_elite and spots and spots[0].get("tier", 1) >= 4:
            save_ev = _short_name(spots[0]["event_name"])

        raw.append({
            "name":    name,    "owgr":  owgr,
            "win_prob":  round(win_prob, 1),  "top10_prob": round(top10_prob, 1),
            "pick_pct":  round(pct, 1),
            "headshot_url":           "",
            "form_label":             _form_label(float(stats.get("sg_total", 0))),
            "save_event":             save_ev,
            "rival_burn_pct":         round(burn, 1),
            "leader_exclusivity_pct": round(burn, 1),
            "is_elite":    is_elite,
            "future_spots": spots,
            # Raw SG values — browser recomputes course_fit when sliders move
            "sg_ott":       round(float(stats.get("sg_ott",  0)), 4),
            "sg_app":       round(float(stats.get("sg_app",  0)), 4),
            "sg_arg":       round(float(stats.get("sg_arg",  0)), 4),
            "sg_putt":      round(float(stats.get("sg_putt", 0)), 4),
            "history_bonus": round(hist_bonus, 4),
            # Pre-normalized component scores (0-100, except ps_v added below)
            "_wt": wt_raw, "_fv": fv_raw,
            "_la": la_raw, "_pl": pl_raw, "_le": le_raw,
        })

    if not raw:
        return []

    def nv(key):
        return _normalize([c[key] for c in raw])

    wt_n = nv("_wt"); fv_n = nv("_fv")
    la_n = nv("_la"); pl_n = nv("_pl"); le_n = nv("_le")

    result = []
    for i, c in enumerate(raw):
        d = {k: v for k, v in c.items() if not k.startswith("_")}
        d.update({
            "wt_n": round(wt_n[i], 2), "fv_n": round(fv_n[i], 2), "ps_v": ps_v,
            "la_n": round(la_n[i], 2), "pl_n": round(pl_n[i], 2), "le_n": round(le_n[i], 2),
        })
        result.append(d)
    return result


def generate_static_html():
    """Generate golf_picks.html — a self-contained file you can double-click."""
    print("\n  ⛳  Golf One-and-Done Picks Advisor — Generating Static HTML")
    print("  ─────────────────────────────────────────────────────────────")

    maybe_refresh_monday()

    api_key = get_api_key()
    if not api_key:
        print("  ERROR: DataGolf API key required. Run:  python golf_picks.py --config")
        sys.exit(1)

    cfg = load_cfg()

    print("  → Fetching PGA Tour schedule...")
    sched = fetch_schedule(api_key)

    print("  → Detecting current tournament...")
    tournament = detect_tournament(sched, api_key) or {
        "event_name": "Unknown Tournament", "course": "Unknown Course",
        "purse": 8_000_000, "start_date": str(date.today()),
        "end_date": str(date.today() + timedelta(days=3)),
        "value_tier": 2, "is_major": False, "is_elevated": False, "event_id": None,
    }
    print(f"     {tournament['event_name']}  @  {tournament.get('course', '')}")

    print("  → Fetching field...")
    field = fetch_field(api_key) or fetch_espn_field("")
    print(f"     {len(field)} players")
    if not field:
        print("  ERROR: Could not retrieve field.")
        sys.exit(1)

    print("  → Fetching rankings & SG stats...")
    rankings = fetch_rankings(api_key)

    print("  → Fetching win probabilities...")
    predictions = fetch_predictions(api_key)

    event_id = tournament.get("event_id")
    course_history = {}
    if event_id:
        print("  → Fetching course history...")
        course_history = fetch_course_history(api_key, event_id)

    rem = remaining_schedule(sched, tournament.get("event_name", ""))
    print(f"  → {len(rem)} events remaining this season")

    used_data  = load_used()
    used_lower = used_names_set(used_data)
    sg_profile = _course_profile(tournament.get("course", ""))

    tmp = [{"name": pl["name"],
            "win_prob": float(predictions.get(pl["dg_id"], {}).get("win_prob", 0.5))}
           for pl in field]
    pick_pcts   = estimate_pick_pcts(tmp)
    total_members = cfg.get("league", {}).get("total_members", 20)
    usage_rates = fetch_mpsp_usage(total_members)

    print("  → Scoring all eligible players...")
    player_data = _build_static_player_data(
        field, rankings, predictions, tournament, rem, course_history,
        used_lower, sg_profile, pick_pcts, usage_rates,
    )
    print(f"     {len(player_data)} players embedded")

    purse    = tournament.get("purse", 0)
    baseline = {
        "tournament":   tournament.get("event_name", ""),
        "course":       tournament.get("course", ""),
        "purse":        f"${purse:,.0f}" if purse else "—",
        "field_size":   len(field),
        "sg": {
            "sg_ott":  sg_profile.get("sg_ott",  0.25),
            "sg_app":  sg_profile.get("sg_app",  0.35),
            "sg_arg":  sg_profile.get("sg_arg",  0.15),
            "sg_putt": sg_profile.get("sg_putt", 0.25),
        },
        "weights":      MODE_WEIGHTS,
        "weather":      None,
        "weather_sg":   None,
        "ev_contests":  _ev_contests_this_week(tournament),
        "profile_type": sg_profile.get("type", "balanced"),
    }
    history = load_pick_history()

    if not UI_HTML.exists():
        print(f"  ERROR: Template not found: {UI_HTML}")
        sys.exit(1)

    template = UI_HTML.read_text(encoding="utf-8")
    generated_at = datetime.now().strftime("%Y-%m-%d %H:%M")
    static_script = (
        f'<script>\n'
        f'// Generated by golf_picks.py on {generated_at}\n'
        f'const __STATIC_BASELINE__    = {json.dumps(baseline, separators=(",",":"))};\n'
        f'const __STATIC_PLAYER_DATA__ = {json.dumps(player_data, separators=(",",":"))};\n'
        f'const __STATIC_HISTORY__     = {json.dumps(history, separators=(",",":"))};\n'
        f'</script>\n'
    )

    html = (template
        .replace("__TOURNAMENT_NAME__", tournament.get("event_name", "—"))
        .replace("__COURSE__",          tournament.get("course", "—"))
        .replace("__PURSE__",           f"${purse:,.0f}" if purse else "—")
        .replace("__FIELD_SIZE__",      str(len(field)))
        .replace("__STANDINGS__",       "")
        .replace("__PROFILE_TYPE__",    sg_profile.get("type", "balanced"))
        .replace("<body>",              f"<body>\n{static_script}", 1)
    )

    STATIC_HTML_OUTPUT.write_text(html, encoding="utf-8")
    size_kb = STATIC_HTML_OUTPUT.stat().st_size // 1024
    print(f"\n  ✓  Generated: {STATIC_HTML_OUTPUT}  ({size_kb} KB)")
    print(f"     Double-click to open, or:  open '{STATIC_HTML_OUTPUT}'")


# ══════════════════════════════════════════════════════════════════════════════
# WEB UI  (python golf_picks.py --ui)
# ══════════════════════════════════════════════════════════════════════════════

def load_pick_history() -> list:
    if PICK_HISTORY_FILE.exists():
        try:
            return json.loads(PICK_HISTORY_FILE.read_text())
        except Exception:
            pass
    return []


def fetch_mpsp_usage(total_members: int = 20) -> dict:
    """Fetch season-long player usage rates from MPSP public page."""
    try:
        r = requests.get(
            f"{MPSP_BASE}/golfers_used_compare/total_golfer_usages",
            timeout=10,
            headers={"User-Agent": "golf-picks-advisor/1.0"},
        )
        if r.status_code != 200:
            return {}
        html = r.text
        counts = {}
        for m in re.finditer(
            r'<td[^>]*>([A-Z][a-z]+(?:[\s\-][A-Z][a-z]+)+)</td>\s*<td[^>]*>(\d+)</td>',
            html,
        ):
            counts[m.group(1).strip()] = int(m.group(2))
        if not counts:
            return {}
        tm = max(total_members, 1)
        return {n: round(min(c / tm * 100, 100), 1) for n, c in counts.items()}
    except Exception as e:
        print(f"    [WARN] MPSP usage fetch failed: {e}")
        return {}


def estimate_pick_pcts(candidates: list) -> dict:
    """Estimate weekly pick% from win probabilities (pre-deadline proxy)."""
    powered = {c["name"]: max(c.get("win_prob", 0.01), 0.01) ** 0.6 for c in candidates}
    tp = sum(powered.values()) or 1.0
    return {n: round(min(v / tp * 100, 30.0), 1) for n, v in powered.items()}


def _lev_label(pick_pct: float) -> str:
    if pick_pct >= 20: return "CHALK"
    if pick_pct >= 10: return "popular"
    if pick_pct >= 5:  return "moderate"
    if pick_pct >= 2:  return "low"
    return "contrarian"


def _form_label(sg_total: float) -> str:
    if sg_total > 1.5:  return "🔥"
    if sg_total > 0.5:  return "✅"
    if sg_total < -0.5: return "❄️"
    return ""


def _fuzzy_lookup(name: str, mapping: dict) -> float:
    """Fuzzy-match name against a {name: float} dict."""
    if name in mapping:
        return float(mapping[name])
    nl = name.lower()
    for k, v in mapping.items():
        if difflib.SequenceMatcher(None, nl, k.lower()).ratio() > 0.80:
            return float(v)
    return 0.0


def filter_schedule_for_contest(rem: list, contest: str, cfg: dict) -> list:
    if contest == "year":
        return rem
    if contest == "majors":
        return [e for e in rem if e.get("is_major")]
    if contest == "cup":
        return [e for e in rem if
                any(kw in e.get("event_name", "").lower() for kw in CUP_KEYWORDS)
                or e.get("value_tier", 1) >= 4]
    if contest in ("seg1", "seg2", "seg3", "seg4"):
        segs = cfg.get("league", {}).get("segments", {})
        seg  = segs.get(contest, {})
        start_ev = seg.get("start_event", "").lower()
        end_ev   = seg.get("end_event", "").lower()
        if not start_ev:
            return rem
        out, in_seg = [], False
        for e in rem:
            en = e.get("event_name", "").lower()
            if start_ev in en:
                in_seg = True
            if in_seg:
                out.append(e)
            if end_ev and end_ev in en:
                in_seg = False
        return out if out else rem
    return rem


_UI_FIELDS = frozenset({
    "name", "owgr", "win_prob", "top10_prob", "pick_pct",
    "headshot_url", "form_label", "save_event", "rival_burn_pct",
    "leader_exclusivity_pct", "is_elite", "future_spots", "lev_label",
    "final_score",
})


def score_field_ui(
    field:          list,
    rankings:       dict,
    predictions:    dict,
    tournament:     dict,
    rem_schedule:   list,
    course_history: dict,
    used_lower:     set,
    sg_profile:     dict,
    weights:        dict,
    pick_pcts:      dict = None,
    usage_rates:    dict = None,
) -> list:
    """Score the field with 7 components for the web UI."""
    course   = tournament.get("course", "")
    purse    = float(tournament.get("purse", 0))
    cur_tier = int(tournament.get("value_tier", 2))
    profile  = sg_profile or _course_profile(course)

    all_purses = [float(e.get("purse", 0)) for e in rem_schedule] + [purse]
    purse_norm = purse / (max(all_purses) or 1)

    pick_pcts   = pick_pcts   or {}
    usage_rates = usage_rates or {}

    candidates = []
    for pl in field:
        dg_id = pl["dg_id"]
        name  = pl["name"]
        norm  = _normalize_name(name)
        if norm in used_lower:
            continue
        if any(difflib.SequenceMatcher(None, norm, u).ratio() > 0.85 for u in used_lower):
            continue
        stats = rankings.get(dg_id, {})
        preds = predictions.get(dg_id, {})
        if not stats and not preds:
            continue
        if stats.get("name"):
            name = stats["name"]

        owgr       = int(stats.get("owgr",    999))
        win_prob   = float(preds.get("win_prob",      0.5))
        top10_prob = float(preds.get("top10_prob",    5.0))

        hist_bonus, hist_sum = _history_bonus(name, course_history)
        wt_raw = win_prob * 3.0 + top10_prob
        cf_raw = _sg_course_fit(stats, profile) + hist_bonus
        fv_raw = future_value_score(stats, rem_schedule, cur_tier)
        ps_raw = purse_norm

        pct  = _fuzzy_lookup(name, pick_pcts)
        burn = _fuzzy_lookup(name, usage_rates)
        la_raw = max(0.0, 100.0 - burn) / 100.0
        pl_raw = max(0.0, 1.0 - pct / 33.0)
        le_raw = burn / 100.0

        is_elite = owgr <= ELITE_RANK_CUTOFF
        spots    = best_future_spots(stats, rem_schedule)
        save_ev  = ""
        if is_elite and spots and spots[0].get("tier", 1) >= 4:
            save_ev = _short_name(spots[0]["event_name"])

        candidates.append({
            "name":                   name,
            "owgr":                   owgr,
            "win_prob":               round(win_prob, 1),
            "top10_prob":             round(top10_prob, 1),
            "pick_pct":               round(pct, 1),
            "headshot_url":           "",
            "form_label":             _form_label(float(stats.get("sg_total", 0))),
            "save_event":             save_ev,
            "rival_burn_pct":         round(burn, 1),
            "leader_exclusivity_pct": round(burn, 1),
            "is_elite":               is_elite,
            "future_spots":           spots,
            "_wt": wt_raw, "_cf": cf_raw, "_fv": fv_raw,
            "_ps": ps_raw, "_la": la_raw, "_pl": pl_raw, "_le": le_raw,
        })

    if not candidates:
        return []

    def nv(key):
        return _normalize([c[key] for c in candidates])

    wt_n = nv("_wt"); cf_n = nv("_cf"); fv_n = nv("_fv")
    la_n = nv("_la"); pl_n = nv("_pl"); le_n = nv("_le")
    ps_v = purse_norm * 100

    wsum = sum(weights.values()) or 1.0
    w = {k: v / wsum for k, v in weights.items()}

    for i, c in enumerate(candidates):
        score = (w.get("win_top10",          0) * wt_n[i] +
                 w.get("course_fit",         0) * cf_n[i] +
                 w.get("future_value",       0) * fv_n[i] +
                 w.get("purse_size",         0) * ps_v   +
                 w.get("league_advantage",   0) * la_n[i] +
                 w.get("pick_leverage",      0) * pl_n[i] +
                 w.get("leader_exclusivity", 0) * le_n[i])
        c["final_score"] = round(score, 1)
        c["lev_label"]   = _lev_label(c["pick_pct"])

    candidates.sort(key=lambda x: x["final_score"], reverse=True)
    return [{k: v for k, v in c.items() if k in _UI_FIELDS} for c in candidates[:10]]


def _ev_contests_this_week(tournament: dict) -> list:
    out  = ["year"]
    name = tournament.get("event_name", "").lower()
    if tournament.get("is_major"):
        out.append("majors")
    if (any(kw in name for kw in CUP_KEYWORDS)
            or tournament.get("value_tier", 1) >= 3
            or tournament.get("is_elevated")):
        out.append("cup")
    return out


# ── Global state shared with HTTP handler ────────────────────────────────────
_APP_STATE: dict = {}


class _GolfHandler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        pass  # suppress default access log

    def _send_json(self, data, status: int = 200):
        body = json.dumps(data).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _send_html(self, html: str, status: int = 200):
        body = html.encode()
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        path = urlparse(self.path).path
        if path in ("/", "/index.html"):
            self._serve_html()
        elif path == "/baseline.json":
            self._send_json(_APP_STATE.get("baseline", {}))
        elif path == "/history":
            self._send_json(load_pick_history())
        else:
            self.send_response(404)
            self.end_headers()

    def do_POST(self):
        path = urlparse(self.path).path
        if path == "/run":
            try:
                length = int(self.headers.get("Content-Length", 0))
                body   = json.loads(self.rfile.read(length))
                result = self._run_model(body)
                self._send_json(result)
            except Exception as e:
                self._send_json({"error": str(e)}, 500)
        else:
            self.send_response(404)
            self.end_headers()

    def _serve_html(self):
        st  = _APP_STATE
        trn = st.get("tournament", {})
        if not UI_HTML.exists():
            self._send_html("<pre>golf_picks_ui.html not found</pre>", 500)
            return
        template = UI_HTML.read_text(encoding="utf-8")
        purse = trn.get("purse", 0)
        standings_html = ""
        standings = st.get("standings", [])
        if standings:
            parts = [f"#{i+1} {t['name']}" for i, t in enumerate(standings[:5])]
            standings_html = "Standings: " + "  |  ".join(parts)
        prof_type = st.get("sg_profile", {}).get("type", "balanced")
        html = (template
            .replace("__TOURNAMENT_NAME__", trn.get("event_name", "—"))
            .replace("__COURSE__",          trn.get("course", "—"))
            .replace("__PURSE__",           f"${purse:,.0f}" if purse else "—")
            .replace("__FIELD_SIZE__",      str(st.get("field_size", "—")))
            .replace("__STANDINGS__",       standings_html)
            .replace("__PROFILE_TYPE__",    prof_type)
        )
        self._send_html(html)

    def _run_model(self, body: dict) -> dict:
        st      = _APP_STATE
        contest = body.get("contest", "year")
        sg_raw  = body.get("sg", {})
        wt_body = body.get("weights", {})
        cfg     = st.get("cfg", {})

        # Build SG profile from UI sliders (values are 0-1 fractions)
        sg_profile = {
            "sg_ott":  float(sg_raw.get("sg_ott",  0.25)),
            "sg_app":  float(sg_raw.get("sg_app",  0.35)),
            "sg_arg":  float(sg_raw.get("sg_arg",  0.15)),
            "sg_putt": float(sg_raw.get("sg_putt", 0.25)),
            "type":    "custom",
        }
        total = sum(sg_profile[k] for k in ("sg_ott", "sg_app", "sg_arg", "sg_putt"))
        if total > 0:
            for k in ("sg_ott", "sg_app", "sg_arg", "sg_putt"):
                sg_profile[k] /= total

        rem_for_contest = filter_schedule_for_contest(st["rem_schedule"], contest, cfg)

        result = {}
        for mode in ("conservative", "balanced", "chase"):
            raw_w = wt_body.get(mode, MODE_WEIGHTS[mode])
            # Convert percent (0-100) to fraction if the UI sends integers
            if raw_w and max(raw_w.values(), default=0) > 1.5:
                raw_w = {k: v / 100.0 for k, v in raw_w.items()}
            result[mode] = score_field_ui(
                field          = st["field"],
                rankings       = st["rankings"],
                predictions    = st["predictions"],
                tournament     = st["tournament"],
                rem_schedule   = rem_for_contest,
                course_history = st["course_history"],
                used_lower     = st["used_lower"],
                sg_profile     = sg_profile,
                weights        = raw_w,
                pick_pcts      = st["pick_pcts"],
                usage_rates    = st["usage_rates"],
            )
        return result


def cmd_ui():
    """Launch the interactive web UI at http://localhost:5051."""
    print("\n  ⛳  Golf One-and-Done Picks Advisor — Web UI")
    print("  ─────────────────────────────────────────────────")

    maybe_refresh_monday()

    api_key = get_api_key()
    if not api_key:
        print("  ERROR: DataGolf API key required. Run:  python golf_picks.py --config")
        sys.exit(1)

    cfg = load_cfg()

    print("  → Fetching PGA Tour schedule...")
    sched = fetch_schedule(api_key)

    print("  → Detecting current tournament...")
    tournament = detect_tournament(sched, api_key) or {
        "event_name": "Unknown Tournament", "course": "Unknown Course",
        "purse": 8_000_000, "start_date": str(date.today()),
        "end_date": str(date.today() + timedelta(days=3)),
        "value_tier": 2, "is_major": False, "is_elevated": False, "event_id": None,
    }
    print(f"     {tournament['event_name']}  @  {tournament.get('course', '')}")

    print("  → Fetching field...")
    field = fetch_field(api_key) or fetch_espn_field("")
    print(f"     {len(field)} players")
    if not field:
        print("  ERROR: Could not retrieve field.")
        sys.exit(1)

    print("  → Fetching rankings & SG stats...")
    rankings = fetch_rankings(api_key)

    print("  → Fetching win probabilities...")
    predictions = fetch_predictions(api_key)

    event_id = tournament.get("event_id")
    course_history = {}
    if event_id:
        print("  → Fetching course history...")
        course_history = fetch_course_history(api_key, event_id)

    rem = remaining_schedule(sched, tournament.get("event_name", ""))
    print(f"  → {len(rem)} events remaining this season")

    used_data  = load_used()
    used_lower = used_names_set(used_data)

    sg_profile = _course_profile(tournament.get("course", ""))

    # Build candidate list for pick% estimation
    tmp = [{"name": pl["name"],
            "win_prob": float(predictions.get(pl["dg_id"], {}).get("win_prob", 0.5))}
           for pl in field]
    print("  → Estimating pick percentages...")
    pick_pcts = estimate_pick_pcts(tmp)

    total_members = cfg.get("league", {}).get("total_members", 20)
    print("  → Fetching MPSP player usage...")
    usage_rates = fetch_mpsp_usage(total_members)
    if not usage_rates:
        print("     (MPSP unavailable — league advantage estimated from win probability)")

    purse = tournament.get("purse", 0)
    baseline = {
        "tournament":   tournament.get("event_name", ""),
        "course":       tournament.get("course", ""),
        "purse":        f"${purse:,.0f}" if purse else "—",
        "field_size":   len(field),
        "sg": {
            "sg_ott":  sg_profile.get("sg_ott",  0.25),
            "sg_app":  sg_profile.get("sg_app",  0.35),
            "sg_arg":  sg_profile.get("sg_arg",  0.15),
            "sg_putt": sg_profile.get("sg_putt", 0.25),
        },
        "weights":      MODE_WEIGHTS,
        "weather":      None,
        "weather_sg":   None,
        "ev_contests":  _ev_contests_this_week(tournament),
        "profile_type": sg_profile.get("type", "balanced"),
    }

    _APP_STATE.update({
        "field":          field,
        "rankings":       rankings,
        "predictions":    predictions,
        "tournament":     tournament,
        "rem_schedule":   rem,
        "course_history": course_history,
        "used_lower":     used_lower,
        "sg_profile":     sg_profile,
        "pick_pcts":      pick_pcts,
        "usage_rates":    usage_rates,
        "baseline":       baseline,
        "standings":      [],
        "field_size":     len(field),
        "cfg":            cfg,
    })

    if not UI_HTML.exists():
        print(f"\n  ERROR: UI template not found: {UI_HTML}")
        print("  Make sure golf_picks_ui.html is in the same directory as golf_picks.py.")
        sys.exit(1)

    server = HTTPServer(("127.0.0.1", UI_PORT), _GolfHandler)
    url    = f"http://localhost:{UI_PORT}"
    print(f"\n  Server running at  {url}")
    print("  Press Ctrl+C to stop.\n")
    threading.Timer(0.6, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n  Stopped.")


# ══════════════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        prog="golf_picks.py",
        description="One-and-Done PGA Tour Picks Advisor",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""\
Examples:
  python golf_picks.py                          # This week's top 10 picks
  python golf_picks.py --focus driving          # Override SG focus to driving
  python golf_picks.py --focus approach         # Override SG focus to approach
  python golf_picks.py --sg-weights ott=0.4,app=0.4,arg=0.1,putt=0.1  # Custom weights
  python golf_picks.py --used "Scottie Scheffler"   # Log a player as used
  python golf_picks.py --show-used              # See used players list
  python golf_picks.py --reset                  # New season — clear used list
  python golf_picks.py --refresh                # Flush cache, re-fetch everything
  python golf_picks.py --config                 # Update DataGolf API key

SG focus presets: driving, approach, putting, arg, balanced, ballstriking
""")
    parser.add_argument("--used",       metavar="PLAYER", help="Mark PLAYER as used this season")
    parser.add_argument("--show-used",  action="store_true", help="Show used players list")
    parser.add_argument("--reset",      action="store_true", help="Reset used players (new season)")
    parser.add_argument("--refresh",    action="store_true", help="Clear cache and refresh all data")
    parser.add_argument("--config",     action="store_true", help="Set/update DataGolf API key")
    parser.add_argument("--focus",      metavar="PRESET",
                        choices=list(SG_FOCUS_PRESETS.keys()),
                        help="Override SG focus: driving, approach, putting, arg, balanced, ballstriking")
    parser.add_argument("--sg-weights", metavar="WEIGHTS",
                        help="Custom SG weights, e.g. ott=0.4,app=0.4,arg=0.1,putt=0.1")
    parser.add_argument("--ui",            action="store_true",
                        help=f"Launch interactive web UI at http://localhost:{UI_PORT}")
    parser.add_argument("--generate-html", action="store_true",
                        help=f"Generate self-contained {STATIC_HTML_OUTPUT.name} (double-click to open)")
    args = parser.parse_args()

    # ── Simple sub-commands ───────────────────────────────────────────────────
    if args.ui:
        cmd_ui()
        return
    if args.generate_html:
        generate_static_html()
        return
    if args.config:
        cmd_config()
        return
    if args.show_used:
        cmd_show_used()
        return
    if args.reset:
        cmd_reset()
        return
    if args.used:
        cmd_mark_used(args.used)
        return
    if args.refresh:
        clear_cache()

    # ── Resolve SG override ───────────────────────────────────────────────────
    sg_override = None
    if args.sg_weights:
        try:
            parts = {}
            for token in args.sg_weights.split(","):
                k, v = token.strip().split("=")
                parts[f"sg_{k.strip()}"] = float(v.strip())
            total = sum(parts.values())
            if abs(total - 1.0) > 0.01:
                print(f"  [WARN] SG weights sum to {total:.2f}, not 1.0 — normalizing.")
                parts = {k: v / total for k, v in parts.items()}
            parts["type"] = "custom"
            sg_override = parts
        except Exception:
            print("  [ERROR] Invalid --sg-weights format. Use: ott=0.4,app=0.4,arg=0.1,putt=0.1")
            sys.exit(1)
    elif args.focus:
        sg_override = SG_FOCUS_PRESETS[args.focus]

    # ── Weekly picks run ──────────────────────────────────────────────────────
    maybe_refresh_monday()
    print("\n  ⛳  Golf One-and-Done Picks Advisor  —  fetching data...\n")

    api_key = get_api_key()
    if not api_key:
        print("  ERROR: DataGolf API key is required.")
        print("  Run:  python golf_picks.py --config")
        sys.exit(1)

    # 1. Schedule
    print("  → Fetching PGA Tour schedule...")
    sched = fetch_schedule(api_key)
    print(f"     {len(sched)} events found")

    # 2. Detect current tournament
    print("  → Detecting current tournament...")
    tournament = detect_tournament(sched, api_key)
    if not tournament:
        print("  [WARN] Could not detect tournament — check schedule data.")
        tournament = {
            "event_name": "Unknown Tournament",
            "course":     "Unknown Course",
            "purse":      8_000_000,
            "start_date": str(date.today()),
            "end_date":   str(date.today() + timedelta(days=3)),
            "value_tier": 2,
            "is_major":   False,
            "is_elevated":False,
            "event_id":   None,
        }
    t_name = tournament.get("event_name", "")
    t_course = tournament.get("course", "")
    print(f"     {t_name}  @  {t_course}")

    # 3. Field
    print("  → Fetching tournament field...")
    field = fetch_field(api_key)
    if not field:
        print("  [WARN] DataGolf field empty — trying ESPN...")
        field = fetch_espn_field("")
    print(f"     {len(field)} players in field")
    if not field:
        print("  ERROR: Could not retrieve field. Cannot score players.")
        sys.exit(1)

    # 4. Rankings + SG
    print("  → Fetching player rankings & strokes-gained stats...")
    rankings = fetch_rankings(api_key)
    print(f"     {len(rankings)} players with SG data")

    # 5. Predictions
    print("  → Fetching win/top-10 probabilities...")
    predictions = fetch_predictions(api_key)
    print(f"     {len(predictions)} players with prediction data")

    # 6. Course history
    event_id = tournament.get("event_id")
    course_history = {}
    if event_id:
        print(f"  → Fetching course history (event {event_id})...")
        course_history = fetch_course_history(api_key, event_id)
        print(f"     {len(course_history)} players with historical data")
    else:
        print("  → Skipping course history (no event ID in schedule)")

    # 7. Remaining schedule
    rem = remaining_schedule(sched, t_name)
    print(f"  → {len(rem)} events remaining this season")

    # 8. Used players
    used_data  = load_used()
    used_lower = used_names_set(used_data)
    used_count = len(used_lower)
    print(f"  → {used_count} players already used this season\n")

    # 9. Score
    print("  → Scoring eligible players...")
    scored = score_field(
        field=field,
        rankings=rankings,
        predictions=predictions,
        tournament=tournament,
        rem_schedule=rem,
        course_history=course_history,
        used_lower=used_lower,
        sg_override=sg_override,
    )
    print(f"     {len(scored)} eligible players scored\n")

    if not scored:
        print("  No eligible players to recommend.")
        print("  (All players may be used, or data may be missing.)")
        sys.exit(0)

    # 10. Add reasoning for top 10
    for p in scored[:10]:
        p["reason"] = generate_reason(p, tournament, rem)

    # 11. Print report
    print_report(tournament, scored, used_count, rem, sg_profile=sg_override)


if __name__ == "__main__":
    main()


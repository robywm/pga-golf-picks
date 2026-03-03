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

  Contests & strategy:
  • Tracks 4 season segments, Commissioner's Cup (8 signature events),
    Majors contest (4 majors), and year-long — each with separate standings
  • Fetches league-wide golfer usage from mpsp.protourfantasygolf.com so
    picks account for "competitive availability" (how rare your access is)
  • Reads your standings in each contest and sets Chase / Conservative /
    Balanced strategy mode, adjusting scoring weights accordingly
  • Use --league-setup to configure your team name and segment boundaries
  • Use --contest to focus analysis on a specific competition
  • Use --show-standings to see your position in all active contests
"""

import argparse
import difflib
import json
import math
import os
import re
import sys
import time
from datetime import date, datetime, timedelta
from pathlib import Path
from typing import Optional

try:
    import requests
except ImportError:
    print("Missing dependency. Run:  pip install requests")
    sys.exit(1)

# ══════════════════════════════════════════════════════════════════════════════
# PATHS & CONSTANTS
# ══════════════════════════════════════════════════════════════════════════════

BASE_DIR  = Path(__file__).parent
DATA_DIR  = BASE_DIR / "golf_data"
CACHE_DIR = DATA_DIR / "cache"
USED_FILE = DATA_DIR / "used_players.json"
CFG_FILE  = DATA_DIR / "config.json"

DATA_DIR.mkdir(exist_ok=True)
CACHE_DIR.mkdir(exist_ok=True)

DG_BASE   = "https://feeds.datagolf.com"
ESPN_BASE = "https://site.api.espn.com/apis/site/v2/sports/golf"
MPSP_BASE = "https://mpsp.protourfantasygolf.com"

# ── Scoring weights by strategy mode (each must sum to 1.0) ──────────────────
# league_advantage = how rare your access to this player is vs. the league

WEIGHTS_BALANCED = {
    "win_top10":        0.33,   # Win prob + top-10 probability this week
    "course_fit":       0.21,   # SG profile vs course demands + history bonus
    "future_value":     0.20,   # Expected future earnings × event-tier fit
    "purse_size":       0.07,   # How valuable is this week's purse
    "league_advantage": 0.10,   # Competitive scarcity: fewer others can use → rare edge
    "pick_leverage":    0.09,   # Contrarian value: lower pick % = harder to copy = leverage
}
WEIGHTS_CHASE = {               # Chasing top 10 — differentiate from the pack
    "win_top10":        0.33,   # Reduced: raw win prob still matters but not everything
    "course_fit":       0.15,   # Slightly reduced
    "future_value":     0.09,   # Future value matters less when you need ground now
    "purse_size":       0.06,
    "league_advantage": 0.09,
    "pick_leverage":    0.28,   # Key insight: chalk earners move up WITH the pack — you need to
                                # differentiate. Low-owned picks with real win prob gain you ground.
}
WEIGHTS_CONSERVATIVE = {        # Near top in standings — protect the lead
    "win_top10":        0.24,
    "course_fit":       0.23,
    "future_value":     0.26,
    "purse_size":       0.07,
    "league_advantage": 0.12,
    "pick_leverage":    0.08,   # Reduced: don't need contrarian plays when leading
}

# Back-compat alias (used in reasoning generator which doesn't need mode awareness)
WEIGHTS = WEIGHTS_BALANCED

# Cache TTLs (seconds)
CACHE_TTL = {
    "field":            6 * 3600,
    "rankings":        12 * 3600,
    "predictions":      6 * 3600,
    "schedule":        24 * 3600,
    "history":          7 * 24 * 3600,
    "mpsp_usage":       4 * 3600,
    "mpsp_standings":   1 * 3600,
    "mpsp_picks":      30 * 60,    # 30 min — refreshes as picks come in
    "mpsp_event_idx":   1 * 3600,
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

WINNER_SHARE = 0.18   # Typical PGA Tour winner's share of purse (for earnings estimates)

# Commissioner's Cup — 8 signature events (partial name match)
COMMISSIONER_CUP_KEYWORDS = [
    "pebble beach", "genesis invitational", "arnold palmer invitational",
    "rbc heritage", "miami championship", "truist championship",
    "memorial tournament", "travelers championship",
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
            "win_prob":      float(p.get("win")      or p.get("win_prob")  or 0) * 100,
            "top5_prob":     float(p.get("top_5")    or p.get("top5")      or 0) * 100,
            "top10_prob":    float(p.get("top_10")   or p.get("top10")     or 0) * 100,
            "top20_prob":    float(p.get("top_20")   or p.get("top20")     or 0) * 100,
            "make_cut_prob": float(p.get("make_cut") or p.get("mc")        or 0.70) * 100,
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
# MPSP LEAGUE DATA FETCHERS
# ══════════════════════════════════════════════════════════════════════════════

def _html_get(url: str, timeout: int = 15) -> str:
    """Fetch URL, return raw HTML string (empty string on failure)."""
    try:
        r = requests.get(url, timeout=timeout,
                         headers={"User-Agent": "Mozilla/5.0 golf-picks-advisor/1.0"})
        r.raise_for_status()
        return r.text
    except Exception as e:
        print(f"    [WARN] Could not fetch {url}: {e}")
        return ""

def _strip_html(text: str) -> str:
    """Remove HTML tags and decode common HTML entities."""
    text = re.sub(r'<[^>]+>', '', text)
    for ent, ch in [('&amp;', '&'), ('&lt;', '<'), ('&gt;', '>'),
                    ('&nbsp;', ' '), ('&#39;', "'"), ('&quot;', '"')]:
        text = text.replace(ent, ch)
    return text.strip()

def _parse_html_table(html: str, table_idx: int = 0) -> list[list[str]]:
    """Parse HTML table by index. Returns rows as lists of cleaned cell strings."""
    tables = re.findall(r'<table[^>]*>(.*?)</table>', html, re.DOTALL | re.IGNORECASE)
    if not tables or table_idx >= len(tables):
        return []
    rows = re.findall(r'<tr[^>]*>(.*?)</tr>', tables[table_idx], re.DOTALL | re.IGNORECASE)
    result = []
    for row_html in rows:
        cells = re.findall(r'<t[dh][^>]*>(.*?)</t[dh]>', row_html, re.DOTALL | re.IGNORECASE)
        parsed = [_strip_html(c) for c in cells]
        if any(parsed):
            result.append(parsed)
    return result

def fetch_mpsp_golfer_usage(force: bool = False) -> dict:
    """
    Scrape league-wide golfer usage counts from MPSP site.
    Returns {normalized_player_name: usage_count}.
    """
    ttl = CACHE_TTL["mpsp_usage"]
    if not force:
        cached = cache_read("mpsp_usage", ttl)
        if cached is not None:
            return cached

    html = _html_get(f"{MPSP_BASE}/golfers_used_compare/total_golfer_usages")
    if not html:
        return cache_read("mpsp_usage", 99_999_999) or {}

    usage = {}
    for table_idx in range(5):          # Try first 5 tables
        rows = _parse_html_table(html, table_idx)
        if not rows:
            break
        found = False
        for row in rows:
            if len(row) < 2:
                continue
            name_raw  = row[0].strip()
            count_str = re.sub(r'[^\d]', '', row[1])
            if not count_str or name_raw.lower() in ('golfer', 'player', 'name', ''):
                continue
            try:
                usage[_normalize_name(name_raw)] = int(count_str)
                found = True
            except ValueError:
                pass
        if found:
            break

    if usage:
        cache_write("mpsp_usage", usage)
    return usage

def _parse_standings_rows(html: str) -> list[dict]:
    """Parse individual standings table from HTML.
    Columns expected: Place, PWC, Flag, Team, Owner, Earnings, Earnings Back, ..."""
    entries = []
    for table_idx in range(5):
        rows = _parse_html_table(html, table_idx)
        if not rows:
            continue
        parsed_any = False
        for row in rows:
            if len(row) < 5:
                continue
            rank_str = re.sub(r'[^\d]', '', row[0])
            if not rank_str:
                continue
            try:
                rank = int(rank_str)
            except ValueError:
                continue
            team  = row[3] if len(row) > 3 else ""
            owner = row[4] if len(row) > 4 else ""
            earnings = 0.0
            earnings_back = 0.0
            if len(row) > 5:
                m = re.search(r'[\d,]+', row[5].replace(',', ''))
                if m:
                    try:
                        earnings = float(m.group())
                    except ValueError:
                        pass
            if len(row) > 6:
                m = re.search(r'[\d,]+', row[6].replace(',', ''))
                if m:
                    try:
                        earnings_back = float(m.group())
                    except ValueError:
                        pass
            if rank and (team or owner):
                entries.append({
                    "rank": rank, "team": team, "owner": owner,
                    "earnings": earnings, "earnings_back": earnings_back,
                })
                parsed_any = True
        if parsed_any:
            break
    return entries

def fetch_mpsp_standings(force: bool = False) -> dict:
    """
    Fetch standings for all contests from MPSP site.
    Returns {"year": [...], "majors": [...], "cup": [...], "seg1": [...], ...}
    Each list: [{rank, team, owner, earnings, earnings_back}, ...]
    """
    ttl = CACHE_TTL["mpsp_standings"]
    if not force:
        cached = cache_read("mpsp_standings", ttl)
        if cached is not None:
            return cached

    import datetime
    year = datetime.date.today().year
    result: dict = {}

    # Year-long individual standings
    html = _html_get(f"{MPSP_BASE}/standings/individual")
    year_entries = _parse_standings_rows(html) if html else []
    result["year"] = year_entries

    # Commissioner's Cup — confirmed URL
    html = _html_get(f"{MPSP_BASE}/standings/commissioners_cup")
    result["cup"] = _parse_standings_rows(html) if html else []

    # Majors — only available after first major (Masters) is played
    html = _html_get(f"{MPSP_BASE}/standings/majors")
    majors_entries = _parse_standings_rows(html) if html else []
    result["majors"] = majors_entries

    # Segment standings — site uses changePeriod(season, period) JS:
    #   /standings/individual/{year}/{period}/
    # Segment standings — site JS: changePeriod(season, period) →
    #   /standings/individual/{year}/{period}/
    # Period values: 0=Season, 1=Segment 1, 2=Segment 2, 3=Segment 3, 4=Segment 4
    # Note: early in a segment the data will equal season standings (same events).
    for seg_num in range(1, 5):
        html = _html_get(f"{MPSP_BASE}/standings/individual/{year}/{seg_num}/")
        result[f"seg{seg_num}"] = _parse_standings_rows(html) if html else []

    if result.get("year"):
        cache_write("mpsp_standings", result)
    return result

def fetch_mpsp_current_picks(force: bool = False) -> tuple[dict, bool]:
    """
    Fetch current week's pick counts from the MPSP Golfers Picked Chart.
    Returns ({normalized_name: count}, data_available).
    Data is only available AFTER the weekly lineup deadline.
    Before deadline this returns ({}, False) — use estimate_pick_pcts() as fallback.
    """
    event_idx = _get_current_event_index(force=force)
    if not event_idx:
        return {}, False

    cache_key = f"mpsp_picks_{event_idx}"
    ttl = CACHE_TTL.get("mpsp_picks", 30 * 60)
    if not force:
        cached = cache_read(cache_key, ttl)
        if cached is not None:
            return cached, bool(cached)

    html = _html_get(f"{MPSP_BASE}/golfers_picked/index/{event_idx}")
    if not html or "unavailable" in html.lower():
        return {}, False

    picks: dict = {}
    for table_idx in range(5):
        rows = _parse_html_table(html, table_idx)
        if not rows:
            continue
        found = False
        for row in rows:
            if len(row) < 2:
                continue
            name_raw  = row[0].strip()
            count_str = re.sub(r'[^\d]', '', row[1])
            if not count_str or name_raw.lower() in ('golfer', 'player', 'name', ''):
                continue
            try:
                picks[_normalize_name(name_raw)] = int(count_str)
                found = True
            except ValueError:
                pass
        if found:
            break

    if picks:
        cache_write(cache_key, picks)
    return picks, bool(picks)

def _get_current_event_index(force: bool = False) -> Optional[int]:
    """Detect the current MPSP event index from the weekly_results page."""
    if not force:
        cached = cache_read("mpsp_event_idx", 1 * 3600)
        if cached is not None:
            return cached

    html = _html_get(f"{MPSP_BASE}/weekly_results")
    if not html:
        return None
    m = re.search(r'/golfers_picked/index/(\d+)', html)
    if m:
        idx = int(m.group(1))
        cache_write("mpsp_event_idx", idx)
        return idx
    return None

def estimate_pick_pcts(scored: list[dict], total_members: int) -> dict:
    """
    Estimate weekly pick percentages based on win probability distribution.
    Used as fallback when actual pick data isn't yet available (pre-deadline).
    Returns {player_name: pick_pct} so lookup is by name, not position.

    Logic: in one-and-done leagues, picks concentrate heavily on the top 10-15
    players. We model this by:
      1. Only distributing among players with win_prob >= 1% (realistic contenders)
      2. Using exponent=2.5 so picks skew sharply toward high-probability players
      3. Players below threshold get a flat ~0.5% residual estimate
    This produces realistic ownership: top favorite ~25-40%, second ~15-25%, etc.
    """
    if not scored:
        return {}
    WIN_THRESHOLD = 1.0   # only realistic picks among players with >=1% win prob
    EXPONENT      = 2.5   # steep concentration toward favorites
    RESIDUAL_PCT  = 0.5   # flat estimate for long-shots below threshold

    result: dict = {}
    contenders = [p for p in scored if p.get("win_prob", 0) >= WIN_THRESHOLD]
    tail       = [p for p in scored if p.get("win_prob", 0) <  WIN_THRESHOLD]

    # Assign residual to long-shots first, then distribute remainder to contenders
    tail_total = len(tail) * RESIDUAL_PCT
    for p in tail:
        result[p["name"]] = RESIDUAL_PCT

    remaining_pct = max(100.0 - tail_total, 10.0)
    if contenders:
        raw   = [p.get("win_prob", 0) ** EXPONENT for p in contenders]
        total = sum(raw) or 1.0
        for p, r in zip(contenders, raw):
            result[p["name"]] = round(r / total * remaining_pct, 1)
    return result

def pick_pct_label(pct: float) -> str:
    """Return a human-readable label for a pick percentage."""
    if pct >= 25:   return "CHALK"
    if pct >= 12:   return "popular"
    if pct >= 4:    return "moderate"
    if pct >= 1.5:  return "low"
    return "contrarian"

TOP10_GOAL = 10   # Target finish position for all contests

def my_standings_context(standings: dict, my_team: str, my_owner: str = "") -> dict:
    """
    Find the user's position in each contest.
    Matches on team name OR owner name (case-insensitive substring).
    Returns {contest: {rank, total, earnings, earnings_back, mode, pct_rank,
                       top10_earnings, gap_to_top10, in_top10}}.
    mode is calibrated to a TOP-10 finish goal:
      'conservative' = already in top 10 (protect position)
      'balanced'     = just outside top 10 (#11-20), within striking distance
      'chase'        = rank 21+ (need to climb meaningfully to reach top 10)
    """
    if not my_team and not my_owner:
        return {}
    needles = [s.lower() for s in [my_team, my_owner] if s]
    context: dict = {}
    for contest, entries in standings.items():
        if not entries:
            continue
        total = len(entries)
        my_entry = None
        for e in entries:
            team_l  = e["team"].lower()
            owner_l = e["owner"].lower()
            if any(n in team_l or n in owner_l for n in needles):
                my_entry = e
                break
        if not my_entry:
            continue
        rank     = my_entry["rank"]
        pct_rank = rank / total if total else 0.5
        # Find the #10 player's earnings (top-10 boundary)
        sorted_entries = sorted(entries, key=lambda e: e["rank"])
        top10_entry    = sorted_entries[TOP10_GOAL - 1] if len(sorted_entries) >= TOP10_GOAL else sorted_entries[-1]
        top10_earnings = top10_entry["earnings"]
        gap_to_top10   = max(top10_earnings - my_entry["earnings"], 0)
        in_top10       = rank <= TOP10_GOAL
        # Mode based on distance from top-10 goal
        if in_top10:
            mode = "conservative"
        elif rank <= 20:
            mode = "balanced"
        else:
            mode = "chase"
        context[contest] = {
            "rank":           rank,
            "total":          total,
            "earnings":       my_entry["earnings"],
            "earnings_back":  my_entry["earnings_back"],
            "mode":           mode,
            "pct_rank":       round(pct_rank, 2),
            "top10_earnings": top10_earnings,
            "gap_to_top10":   gap_to_top10,
            "in_top10":       in_top10,
        }
    return context

# ══════════════════════════════════════════════════════════════════════════════
# CONTEST LOGIC
# ══════════════════════════════════════════════════════════════════════════════

def load_league_cfg() -> dict:
    """Load league config section from config.json."""
    return load_cfg().get("league", {})

def save_league_cfg(league: dict):
    cfg = load_cfg()
    cfg["league"] = league
    save_cfg(cfg)

def cmd_setup_league():
    """Interactive league configuration wizard."""
    league = load_league_cfg()
    print("\n  ── LEAGUE SETUP ──────────────────────────────────────────────")
    cur_team = league.get("my_team", "")
    print(f"  Current team name: {cur_team or '(not set)'}")
    new_team = input("  Your team name (Enter to keep): ").strip()
    if new_team:
        league["my_team"] = new_team

    cur_owner = league.get("my_owner", "")
    print(f"  Current owner name (as shown on MPSP): {cur_owner or '(not set)'}")
    new_owner = input("  Your owner name (Enter to keep): ").strip()
    if new_owner:
        league["my_owner"] = new_owner

    cur_members = league.get("total_members", 0)
    print(f"\n  Current total league members: {cur_members or '(auto-detect from standings)'}")
    nm = input("  Total league members (Enter to auto-detect): ").strip()
    if nm.isdigit():
        league["total_members"] = int(nm)

    print("\n  Configure 4 season segments (enter start and end event names).")
    print("  Example: 'Sony Open in Hawaii'  or  'Arnold Palmer Invitational'")
    segments = league.get("segments", [])
    new_segs = []
    for i in range(1, 5):
        cur = segments[i - 1] if i <= len(segments) else {}
        print(f"\n  Segment {i}:")
        cur_start = cur.get("start_event", "")
        cur_end   = cur.get("end_event",   "")
        start = input(f"    Start event [{cur_start or 'not set'}]: ").strip() or cur_start
        end   = input(f"    End event   [{cur_end   or 'not set'}]: ").strip() or cur_end
        new_segs.append({"name": f"Segment {i}", "start_event": start, "end_event": end})
    league["segments"] = new_segs
    save_league_cfg(league)
    print("\n  League configuration saved.\n")

def _events_in_segment(sched: list[dict], seg: dict) -> list[str]:
    """Return event names that fall within a segment (start → end, inclusive)."""
    start_kw = seg.get("start_event", "").lower().strip()
    end_kw   = seg.get("end_event",   "").lower().strip()
    if not start_kw or not end_kw:
        return []
    in_seg, names = False, []
    for ev in sched:
        nl = ev.get("event_name", "").lower()
        if not in_seg:
            if start_kw in nl or nl in start_kw:
                in_seg = True
        if in_seg:
            names.append(ev.get("event_name", ""))
            if end_kw in nl or nl in end_kw:
                break
    return names

def all_contests_for_event(event_name: str, sched: list[dict], league_cfg: dict) -> list[str]:
    """Return every contest label that the given event counts toward."""
    nl = event_name.lower()
    contests = ["year"]
    if any(kw in nl for kw in COMMISSIONER_CUP_KEYWORDS):
        contests.append("cup")
    if any(kw in nl for kw in MAJOR_KEYWORDS):
        contests.append("majors")
    for i, seg in enumerate(league_cfg.get("segments", []), 1):
        seg_names_lower = [n.lower() for n in _events_in_segment(sched, seg)]
        if any(nl in sn or sn in nl for sn in seg_names_lower):
            contests.append(f"seg{i}")
    return list(dict.fromkeys(contests))

def remaining_for_contest(
    sched: list[dict], contest: str, current_name: str, league_cfg: dict
) -> list[dict]:
    """Return future schedule events (after today) that count toward `contest`."""
    today = date.today()
    result = []
    for ev in sched:
        try:
            start = date.fromisoformat(ev["start_date"])
        except (ValueError, TypeError):
            continue
        if start <= today or ev.get("event_name", "") == current_name:
            continue
        if contest in all_contests_for_event(ev["event_name"], sched, league_cfg):
            result.append(ev)
    return result

def get_weights_for_mode(mode: str) -> dict:
    """Return scoring weight dict for the given strategy mode."""
    return {"chase": WEIGHTS_CHASE, "conservative": WEIGHTS_CONSERVATIVE}.get(mode, WEIGHTS_BALANCED)

def detect_total_members(standings: dict, usage_data: dict, cfg_members: int) -> int:
    """Best estimate of total league members for burn-rate calculations."""
    if cfg_members > 0:
        return cfg_members
    # Approximate from year-long standings count
    year_entries = standings.get("year", [])
    if year_entries:
        return max(e["rank"] for e in year_entries)
    # Fall back to max usage seen (top used player ≈ total)
    if usage_data:
        return max(usage_data.values())
    return 100  # last resort default

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

def _league_advantage(name: str, usage_data: dict, total_members: int) -> tuple[float, int, float]:
    """
    Competitive scarcity score for a player.
    Returns (raw_score 0–1, usage_count, pct_burned).

    raw_score = pct of league that has already used this player.
    High pct_burned → you have rare access (most opponents can't pick them) → competitive edge.
    Low pct_burned  → most opponents still have them → no scarcity advantage.
    """
    if not usage_data or total_members <= 0:
        return 0.5, 0, 0.5   # Unknown — neutral
    norm = _normalize_name(name)          # e.g. "rory mcilroy"
    last = norm.split()[-1] if norm else norm   # e.g. "mcilroy"
    usage_count = 0
    # 1. Exact full-name match
    if norm in usage_data:
        usage_count = usage_data[norm]
    else:
        # 2. Last-name match: MPSP often stores just last name ("mcilroy")
        #    or last-name with first initial ("b koepka"). Both share last token.
        for league_name, count in usage_data.items():
            league_last = league_name.split()[-1] if league_name else ""
            if last == league_last:
                usage_count = count
                break
        # 3. Fuzzy fallback for edge cases
        if not usage_count:
            for league_name, count in usage_data.items():
                if difflib.SequenceMatcher(None, norm, league_name).ratio() > 0.78:
                    usage_count = count
                    break
    pct = min(usage_count / total_members, 1.0)
    return pct, usage_count, pct

def score_field(
    field:          list[dict],
    rankings:       dict,
    predictions:    dict,
    tournament:     dict,
    rem_schedule:   list[dict],
    course_history: dict,
    used_lower:     set,
    sg_override:    dict = None,
    usage_data:     dict = None,
    total_members:  int  = 0,
    active_weights: dict = None,
    pick_data:      dict = None,    # {normalized_name: pick_count} — actual MPSP data
    picks_estimated: list = None,   # parallel list of estimated pick pcts (fallback)
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

        # 5. League competitive advantage (how rare is your access to this player?)
        la_raw, la_count, la_pct = _league_advantage(name, usage_data or {}, total_members)

        # 6. Pick leverage (contrarian value — lower weekly pick % = harder to copy)
        #    pick_data holds actual MPSP pick counts this week; picks_estimated is a
        #    parallel list indexed to the field (resolved in the second pass below).
        #    We store placeholder here; actual value filled after building all candidates.
        field_idx = len(candidates)   # index into picks_estimated

        is_elite = owgr <= ELITE_RANK_CUTOFF

        candidates.append({
            "dg_id":          dg_id,
            "name":           name,
            "owgr":           owgr,
            "dg_rank":        dg_rank,
            "sg_total":       float(stats.get("sg_total", 0)),
            "sg_ott":         float(stats.get("sg_ott",   0)),
            "sg_app":         float(stats.get("sg_app",   0)),
            "sg_arg":         float(stats.get("sg_arg",   0)),
            "sg_putt":        float(stats.get("sg_putt",  0)),
            "win_prob":       win_prob,
            "top10_prob":     top10_prob,
            "make_cut_prob":  cut_prob,
            "course_history": hist_summary,
            "is_elite":       is_elite,
            "league_usage":       la_count,
            "league_pct_burned":  round(la_pct * 100, 1),
            "pick_pct":           0.0,   # filled below
            "pick_pct_source":    "",    # 'actual' | 'estimated'
            "_wt_raw":  wt_raw,
            "_cf_raw":  cf_raw,
            "_fv_raw":  fv_raw,
            "_ps_raw":  ps_raw,
            "_la_raw":  la_raw,
            "_pl_raw":  0.0,    # pick_leverage — filled below
            "_field_idx": field_idx,
            "future_spots": best_future_spots(stats, rem_schedule),
        })

    if not candidates:
        return []

    # ── Resolve pick_pct for each candidate ──────────────────────────────────
    # Use actual MPSP data if available, else fall back to estimation.
    total_pick_count = sum((pick_data or {}).values()) or total_members or len(candidates)
    if total_pick_count <= 0:
        total_pick_count = len(candidates)

    for c in candidates:
        if pick_data:
            # Actual post-deadline pick counts
            norm = _normalize_name(c["name"])
            count = 0
            for lname, cnt in (pick_data or {}).items():
                if difflib.SequenceMatcher(None, norm, lname).ratio() > 0.78:
                    count = cnt
                    break
            pct  = count / total_pick_count * 100
            src  = "actual"
        elif picks_estimated and c["name"] in picks_estimated:
            pct = picks_estimated[c["name"]]
            src = "est."
        else:
            pct = 1.0
            src = "est."
        c["pick_pct"]        = round(pct, 1)
        c["pick_pct_source"] = src
        # pick_leverage_raw: 1 - (pick_pct/100), clamped to [0,1]
        # Low pick % → high raw score → high leverage
        c["_pl_raw"] = max(0.0, 1.0 - pct / 100.0)

    # ── Normalize each component across the field ────────────────────────────
    n = len(candidates)

    wt_n = _normalize([c["_wt_raw"] for c in candidates])
    cf_n = _normalize([c["_cf_raw"] for c in candidates])
    fv_n = _normalize([c["_fv_raw"] for c in candidates])
    la_n = _normalize([c["_la_raw"] for c in candidates])
    pl_n = _normalize([c["_pl_raw"] for c in candidates])
    # Purse is a scalar — convert to 0-100 directly, same for all
    ps_val = purse_norm * 100

    # Use mode-specific weights if provided, else balanced defaults
    w = active_weights if active_weights else WEIGHTS_BALANCED

    # Future elite events still available
    elite_remaining = [e for e in rem_schedule if e.get("value_tier", 1) >= 4]

    for i, c in enumerate(candidates):
        wt = wt_n[i]
        cf = cf_n[i]
        fv = fv_n[i]
        ps = ps_val
        la = la_n[i]
        pl = pl_n[i]

        score = (w["win_top10"]        * wt +
                 w["course_fit"]       * cf +
                 w["future_value"]     * fv +
                 w["purse_size"]       * ps +
                 w["league_advantage"] * la +
                 w["pick_leverage"]    * pl)

        c["score_win_top10"]    = round(wt, 1)
        c["score_course_fit"]   = round(cf, 1)
        c["score_future_val"]   = round(fv, 1)
        c["score_purse"]        = round(ps, 1)
        c["score_league_adv"]   = round(la, 1)
        c["score_pick_lev"]     = round(pl, 1)
        c["final_score"]        = round(score, 1)

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

    # ── Pick ownership / leverage ─────────────────────────────────────────────
    chalk   = [p for p in picks if p.get("pick_pct", 0) >= 20]
    leverage = [p for p in picks if p.get("pick_pct", 0) < 5 and p["win_prob"] >= 4]
    src = picks[0].get("pick_pct_source", "est.") if picks else "est."
    src_note = "(actual MPSP picks)" if src == "actual" else "(estimated pre-deadline)"

    if chalk:
        chalk_names = ", ".join(
            p["name"].split(",")[0].title() if "," in p["name"] else p["name"].split()[-1]
            for p in chalk[:4]
        )
        chalk_pcts = " / ".join(f"{p['pick_pct']:.0f}%" for p in chalk[:4])
        print(f"\n  CHALK {src_note}: {chalk_names}  [{chalk_pcts}]")
        print(f"  {_wrap('High pick% players — everyone else is riding them too. Picking chalk keeps you safe when they score, but you gain zero ground when they succeed.', 74, '  ')}")

    if leverage:
        lev_names = ", ".join(
            p["name"].split(",")[0].title() if "," in p["name"] else p["name"].split()[-1]
            for p in leverage[:3]
        )
        lev_pcts = " / ".join(f"{p['pick_pct']:.0f}%" for p in leverage[:3])
        print(f"\n  HIGH LEVERAGE {src_note}: {lev_names}  [{lev_pcts}]")
        print(f"  {_wrap('Low pick% players with meaningful win probability. If they score well you gain on almost everyone in the field — maximum differentiation.', 74, '  ')}")

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

CONTEST_LABELS = {
    "year":   "Year-Long",
    "majors": "Majors",
    "cup":    "Commissioner's Cup",
    "seg1":   "Segment 1",
    "seg2":   "Segment 2",
    "seg3":   "Segment 3",
    "seg4":   "Segment 4",
}

def _print_contest_context(
    standings_ctx:  dict,
    ev_contests:    list[str],
    active_contest: str,
    mode:           str,
):
    """Print league standings (top-10 goal framing) and strategy mode."""
    if not standings_ctx:
        return
    W = 78
    print(f"\n  LEAGUE STANDINGS  (goal: top {TOP10_GOAL} finish in each contest)")
    print("─" * W)
    mode_tags = {
        "chase":        "⚡ CHASE",
        "conservative": "🛡 CONSERVATIVE",
        "balanced":     "⚖ BALANCED",
    }
    for contest, ctx in standings_ctx.items():
        label    = CONTEST_LABELS.get(contest, contest.upper())
        in_ev    = "  ◄ THIS WEEK COUNTS" if contest in ev_contests else ""
        rank     = ctx["rank"]
        total    = ctx["total"]
        earn     = ctx["earnings"]
        g10      = ctx.get("gap_to_top10", 0)
        in_top10 = ctx.get("in_top10", False)
        m_tag    = mode_tags.get(ctx["mode"], "")
        active_m = " ← FOCUS" if contest == active_contest else ""
        if in_top10:
            gap_str = f"  (✓ IN TOP {TOP10_GOAL}!)"
        else:
            gap_str = f"  (${g10:>10,.0f} to top {TOP10_GOAL})"
        print(f"  {label:<24} #{rank:>3}/{total:<3}  ${earn:>12,.0f}{gap_str}  {m_tag}{active_m}{in_ev}")

    mode_hints = {
        "chase":        f"outside top {TOP10_GOAL} — use CHASE (high win-prob, contrarian picks to gain ground)",
        "conservative": f"IN top {TOP10_GOAL} — use CONSERVATIVE (protect position, prioritize future value)",
        "balanced":     f"close to top {TOP10_GOAL} — use BALANCED (push without overreaching)",
    }
    print(f"\n  Suggested for [{CONTEST_LABELS.get(active_contest, active_contest)}]: "
          f"{mode_hints.get(mode, mode)}")


def _contest_remaining_events(
    contest: str, sched: list[dict], tournament: dict, league_cfg: dict
) -> list[dict]:
    """Return events counting toward `contest` from now on, INCLUDING the current week."""
    t_name = tournament.get("event_name", "")
    today  = date.today()
    result = []
    for ev in sched:
        try:
            start = date.fromisoformat(ev["start_date"])
        except (ValueError, TypeError):
            continue
        is_current = ev.get("event_name", "") == t_name
        is_future  = start > today
        if not (is_current or is_future):
            continue
        if contest in all_contests_for_event(ev["event_name"], sched, league_cfg):
            result.append(ev)
    return result


def _wrap(text: str, width: int = 76, indent: str = "  ") -> str:
    """Simple word-wrap helper."""
    words, lines, line = text.split(), [], indent
    for w in words:
        if len(line) + len(w) + 1 > width:
            lines.append(line)
            line = indent + w
        else:
            line += (" " if line != indent else "") + w
    if line.strip():
        lines.append(line)
    return "\n".join(lines)


def _print_contest_decision(
    standings_ctx: dict,
    ev_contests:   list[str],
    sched:         list[dict],
    tournament:    dict,
    league_cfg:    dict,
):
    """
    Compare contests the current event counts toward and recommend which to prioritize.
    Shows remaining events, theoretical max earnings, gap closeability, and a verdict.
    """
    # Only compare if we have standings for ≥2 relevant contests
    compare = [c for c in ev_contests if c in standings_ctx]
    if len(compare) < 2:
        return

    W = 78
    print(f"\n  CONTEST DECISION ANALYSIS")
    print("─" * W)

    rows = []
    for contest in compare:
        ctx   = standings_ctx[contest]
        label = CONTEST_LABELS.get(contest, contest.upper())
        rem_evs  = _contest_remaining_events(contest, sched, tournament, league_cfg)
        n_total  = len(rem_evs)
        n_future = n_total - 1
        max_rem  = sum(ev.get("purse", 0) * WINNER_SHARE for ev in rem_evs)
        max_week = max((ev.get("purse", 0) * WINNER_SHARE for ev in rem_evs), default=0)
        g10      = ctx.get("gap_to_top10", ctx["earnings_back"])
        in_top10 = ctx.get("in_top10", False)
        rows.append({
            "contest":   contest,
            "label":     label,
            "rank":      ctx["rank"],
            "total":     ctx["total"],
            "pct_rank":  ctx["pct_rank"],
            "g10":       g10,
            "in_top10":  in_top10,
            "n_total":   n_total,
            "n_future":  n_future,
            "max_rem":   max_rem,
            "max_week":  max_week,
            "top10_closeable": in_top10 or max_rem >= g10,
            "last_event": n_future == 0,
        })

    # ── Print summary rows ────────────────────────────────────────────────────
    for r in rows:
        status  = "⚠ LAST EVENT THIS WEEK" if r["last_event"] else f"{r['n_future']} events after this"
        if r["in_top10"]:
            gap_s = f"  ✓ IN TOP {TOP10_GOAL}!        "
            close = "maintain position"
        else:
            gap_s = f"  ${r['g10']:>10,.0f} to top {TOP10_GOAL}"
            close = "✓ top-10 reachable" if r["top10_closeable"] else "✗ top-10 out of reach"
        print(f"  {r['label']:<24} #{r['rank']:>3}/{r['total']:<3}  {gap_s}  {status}")
        print(f"  {'':24}  Max remaining: ${r['max_rem']:>10,.0f}  [{close}]")
        print()

    # ── Verdict ───────────────────────────────────────────────────────────────
    seg_rows = [r for r in rows if r["contest"].startswith("seg")]
    cup_rows = [r for r in rows if r["contest"] == "cup"]

    if not seg_rows or not cup_rows:
        return  # can't compare if we don't have both

    seg = seg_rows[0]
    cup = cup_rows[0]

    seg_final        = seg["last_event"]
    seg_top10_reach  = seg["top10_closeable"]
    cup_top10_reach  = cup["top10_closeable"]
    seg_in_top10     = seg["in_top10"]
    cup_in_top10     = cup["in_top10"]

    if seg_in_top10 and cup_in_top10:
        verdict = "BOTH — protect all top-10 positions"
        detail  = (
            f"You're in the top {TOP10_GOAL} in both contests. Play conservatively — "
            f"prioritize high-floor picks (strong top-10 probability) and protect your spots."
        )
    elif seg_in_top10 and not cup_in_top10:
        verdict = "CUP — climb into top 10"
        detail  = (
            f"You're already in the top {TOP10_GOAL} in {seg['label']} — protect it with "
            f"a conservative pick. But the bigger opportunity is Commissioner's Cup "
            f"(#{cup['rank']}/{cup['total']}, ${cup['g10']:,.0f} gap) where you have "
            f"{cup['n_future']} events of runway to crack the top {TOP10_GOAL}."
        )
    elif cup_in_top10 and not seg_in_top10:
        verdict = f"SEG — climb into top 10 in {seg['label']}"
        detail  = (
            f"You're already in the top {TOP10_GOAL} in Commissioner's Cup — protect it. "
            f"Focus this week on {seg['label']} (#{seg['rank']}/{seg['total']}, "
            f"${seg['g10']:,.0f} gap to top {TOP10_GOAL})."
        )
    elif seg_final and not seg_top10_reach and cup_top10_reach:
        verdict = "CUP — top-10 is the goal, Segment 1 is out of reach"
        detail  = (
            f"{seg['label']} ends THIS WEEK and a top-{TOP10_GOAL} finish is out of reach "
            f"(${seg['g10']:,.0f} gap, max this event ~${seg['max_week']:,.0f}). "
            f"Commissioner's Cup is the right target: #{cup['rank']}/{cup['total']}, "
            f"${cup['g10']:,.0f} to top {TOP10_GOAL} with {cup['n_future']} events remaining."
        )
    elif seg_final and seg_top10_reach:
        verdict = "EITHER — top-10 push works for both"
        detail  = (
            f"{seg['label']} ends THIS WEEK but a top-{TOP10_GOAL} finish is still possible "
            f"(${seg['g10']:,.0f} gap vs ~${seg['max_week']:,.0f} max). "
            f"An aggressive pick that earns big this week also boosts your Commissioner's Cup "
            f"position (#{cup['rank']}/{cup['total']}, {cup['n_future']} events left). "
            f"Target maximum win probability."
        )
    elif not seg_top10_reach and cup_top10_reach:
        verdict = "CUP — only top-10 path still open"
        detail  = (
            f"Top-{TOP10_GOAL} in {seg['label']} is out of reach "
            f"(${seg['g10']:,.0f} gap, only ${seg['max_rem']:,.0f} max remaining). "
            f"Commissioner's Cup is your best top-{TOP10_GOAL} opportunity: "
            f"#{cup['rank']}/{cup['total']} with ${cup['g10']:,.0f} to close over "
            f"{cup['n_future']} events."
        )
    elif cup["rank"] < seg["rank"] and cup_top10_reach:
        verdict = "CUP — better positioned for top 10"
        detail  = (
            f"Closer to top {TOP10_GOAL} in Commissioner's Cup (#{cup['rank']}, "
            f"${cup['g10']:,.0f} gap) than {seg['label']} (#{seg['rank']}, "
            f"${seg['g10']:,.0f} gap), and the cup has {cup['n_future']} events of runway."
        )
    else:
        verdict = "BOTH — both top-10 paths are open"
        detail  = (
            f"Top-{TOP10_GOAL} is reachable in both contests. "
            f"Play the model's recommended pick — it optimizes for both simultaneously."
        )

    print(f"  VERDICT: {verdict}")
    print(_wrap(detail))
    print()


def print_report(tournament: dict, scored_by_mode: dict,
                 used_count: int, rem: list[dict], sg_profile: dict = None,
                 standings_ctx: dict = None, ev_contests: list[str] = None,
                 active_contest: str = "year", auto_mode: str = "balanced",
                 sched: list = None, league_cfg: dict = None):
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
    if ev_contests:
        contest_str = "  •  ".join(CONTEST_LABELS.get(c, c) for c in ev_contests)
        print(f"  {'Contests':<12}: {contest_str}")

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

    _print_contest_context(
        standings_ctx or {}, ev_contests or [], active_contest, auto_mode
    )
    if sched and league_cfg:
        _print_contest_decision(
            standings_ctx or {}, ev_contests or [], sched, tournament, league_cfg
        )

    # ── Three mode tables ─────────────────────────────────────────────────────
    MODE_META = {
        "conservative": ("🛡  CONSERVATIVE", f"in top {TOP10_GOAL} — protect position, favor floor & future value"),
        "balanced":     ("⚖  BALANCED",      f"just outside top {TOP10_GOAL} — steady push without overreaching"),
        "chase":        ("🔥 CHASE",          f"chasing top {TOP10_GOAL} — differentiate from the pack; chalk moves everyone up together"),
    }
    any_picks = any(scored_by_mode.get(m) for m in MODE_META)
    if not any_picks:
        print("\n  No eligible picks found. Check your API key, cache, or used-player list.")
        print(DIV + "\n")
        return

    for mode_name in ["conservative", "balanced", "chase"]:
        mode_picks = scored_by_mode.get(mode_name, [])
        if not mode_picks:
            continue
        label, desc = MODE_META[mode_name]
        suggested = "  ◄ SUGGESTED" if mode_name == auto_mode else ""
        print(f"\n{DIV}")
        print(f"  {label}  ({desc}){suggested}")
        print(DIV)
        src_note = "actual" if mode_picks[0].get("pick_pct_source") == "actual" else "est."
        is_chase = mode_name == "chase"
        if is_chase:
            print(f"\n  {'#':<4} {'Player':<26} {'Score':>6}  {'Win%':>5}  {'Top10%':>6}  "
                  f"{'Pick%(' + src_note + ')':>12}  {'DiffWin%':>8}  {'Leverage'}")
            print(f"  {'-'*4} {'-'*26} {'-'*6}  {'-'*5}  {'-'*6}  {'-'*12}  {'-'*8}  {'-'*10}")
        else:
            print(f"\n  {'#':<4} {'Player':<26} {'Score':>6}  {'OWGR':>5}  {'Top10%':>6}  "
                  f"{'Pick%(' + src_note + ')':>12}  {'Leverage'}")
            print(f"  {'-'*4} {'-'*26} {'-'*6}  {'-'*5}  {'-'*6}  {'-'*12}  {'-'*10}")
        for rank, p in enumerate(mode_picks[:5], 1):
            elite = "★" if p["is_elite"] else " "
            name  = (p["name"].title() if "," not in p["name"]
                     else f"{p['name'].split(',')[1].strip()} {p['name'].split(',')[0].strip()}".title())
            pct     = p.get("pick_pct", 0.0)
            win_p   = p.get("win_prob", 0.0)
            diff_win = win_p * (1.0 - pct / 100.0)
            if is_chase:
                print(f"  {rank:<4} {elite}{name:<25} {p['final_score']:>6.1f}  "
                      f"{win_p:>4.1f}%  {p['top10_prob']:>5.1f}%  "
                      f"{pct:>10.1f}%  {diff_win:>7.1f}%  {pick_pct_label(pct)}")
            else:
                print(f"  {rank:<4} {elite}{name:<25} {p['final_score']:>6.1f}  "
                      f"#{p['owgr']:<4}  {p['top10_prob']:>5.1f}%  "
                      f"{pct:>10.1f}%  {pick_pct_label(pct)}")

    # Chase-specific note explaining DiffWin%
    if auto_mode == "chase" or "chase" in scored_by_mode:
        chase_picks = scored_by_mode.get("chase", [])[:5]
        if chase_picks:
            print(f"\n  DiffWin% = Win% × (1 − Pick%) — your exclusive upside when chasing.")
            print(f"  Chalk moves everyone up together; high DiffWin% = you gain ground on the pack.")

    # ── Build union of top-5 candidates, sorted by balanced score ─────────────
    seen_names: set = set()
    all_candidates: list = []
    for mode_name in ["conservative", "balanced", "chase"]:
        for p in scored_by_mode.get(mode_name, [])[:5]:
            if p["name"] not in seen_names:
                seen_names.add(p["name"])
                all_candidates.append(p)
    balanced_rank = {p["name"]: p["final_score"] for p in scored_by_mode.get("balanced", [])}
    all_candidates.sort(key=lambda p: balanced_rank.get(p["name"], 0), reverse=True)

    def _mode_tags(name: str) -> str:
        parts = []
        for mn, short in [("conservative", "CON"), ("balanced", "BAL"), ("chase", "CHZ")]:
            for r, p in enumerate(scored_by_mode.get(mn, [])[:5], 1):
                if p["name"] == name:
                    parts.append(f"{short}#{r}")
                    break
        return "  [" + " · ".join(parts) + "]" if parts else ""

    print(f"\n{DIV}")
    print(f"  PLAYER PROFILES  ({len(all_candidates)} candidates across all modes)")
    print(DIV)

    for p in all_candidates:
        mode_tag = _mode_tags(p["name"])
        flag     = "  ⚠  SAVE FOR LATER" if p.get("save_for_later") else ""
        elite    = "★ " if p["is_elite"] else "  "
        print(f"\n  {elite}{p['name'].upper()}{mode_tag}{flag}")
        print(DIV2)

        # Score bar
        bar_len = int(p["final_score"] / 2)
        bar     = "█" * bar_len + "░" * (50 - bar_len)
        print(f"  Score  {p['final_score']:5.1f}/100  [{bar}]")

        # Score breakdown
        print(f"  Components →  Win/Top10: {p['score_win_top10']:5.1f}  "
              f"Course Fit: {p['score_course_fit']:5.1f}  "
              f"Future Val: {p['score_future_val']:5.1f}  "
              f"Purse: {p['score_purse']:5.1f}  "
              f"Lg Adv: {p.get('score_league_adv', 0):5.1f}  "
              f"Pick Lev: {p.get('score_pick_lev', 0):5.1f}")

        # Pick ownership line
        pct     = p.get("pick_pct", 0.0)
        src     = p.get("pick_pct_source", "est.")
        lv_lbl  = pick_pct_label(pct)
        lv_flag = ""
        if pct >= 25:
            lv_flag = "  ⚠ CHALK — picking with the crowd limits your upside"
        elif pct < 4 and p["win_prob"] >= 5:
            lv_flag = "  ★ HIGH LEVERAGE — strong player, almost nobody taking him"
        print(f"  Pick Ownership: {pct:>5.1f}%  [{lv_lbl}]  ({src}){lv_flag}")

        # League usage context
        lg_used  = p.get("league_usage", 0)
        lg_pct   = p.get("league_pct_burned", 0)
        lg_avail = round(100 - lg_pct, 1)
        lg_note  = (f"  [{lg_used} members used ({lg_pct:.0f}% burned) — "
                    f"{lg_avail:.0f}% of league still has them]"
                    if lg_used > 0 else "  [no league usage data]")
        print(f"  League Access:{lg_note}")

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
    _print_summary(all_candidates, tournament, rem)
    print(f"{DIV}\n")

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
  python golf_picks.py                             # This week's top 10 picks
  python golf_picks.py --contest cup               # Focus on Commissioner's Cup
  python golf_picks.py --contest majors            # Focus on Majors contest
  python golf_picks.py --mode chase                # Force aggressive strategy
  python golf_picks.py --show-standings            # Show your standings in all contests
  python golf_picks.py --league-setup              # Configure team name and segments
  python golf_picks.py --focus driving             # Override SG focus to driving
  python golf_picks.py --sg-weights ott=0.4,app=0.4,arg=0.1,putt=0.1  # Custom weights
  python golf_picks.py --used "Scottie Scheffler"  # Log a player as used
  python golf_picks.py --show-used                 # See used players list
  python golf_picks.py --reset                     # New season — clear used list
  python golf_picks.py --refresh                   # Flush cache, re-fetch everything
  python golf_picks.py --config                    # Update DataGolf API key

Contests: year | cup | majors | seg1 | seg2 | seg3 | seg4
SG focus presets: driving, approach, putting, arg, balanced, ballstriking
Modes: auto (default) | chase | conservative | balanced
""")
    parser.add_argument("--used",           metavar="PLAYER", help="Mark PLAYER as used this season")
    parser.add_argument("--show-used",      action="store_true", help="Show used players list")
    parser.add_argument("--reset",          action="store_true", help="Reset used players (new season)")
    parser.add_argument("--refresh",        action="store_true", help="Clear cache and refresh all data")
    parser.add_argument("--config",         action="store_true", help="Set/update DataGolf API key")
    parser.add_argument("--league-setup",   action="store_true", help="Configure league: team name, segments")
    parser.add_argument("--show-standings", action="store_true", help="Show your standings in all contests")
    parser.add_argument("--contest",        metavar="CONTEST",
                        choices=["year", "cup", "majors", "seg1", "seg2", "seg3", "seg4"],
                        default=None,
                        help="Focus contest for strategy mode: year, cup, majors, seg1-seg4")
    parser.add_argument("--mode",           metavar="MODE",
                        choices=["auto", "chase", "conservative", "balanced"],
                        default="auto",
                        help="Strategy mode override (default: auto — derived from standings)")
    parser.add_argument("--focus",          metavar="PRESET",
                        choices=list(SG_FOCUS_PRESETS.keys()),
                        help="Override SG focus: driving, approach, putting, arg, balanced, ballstriking")
    parser.add_argument("--sg-weights",     metavar="WEIGHTS",
                        help="Custom SG weights, e.g. ott=0.4,app=0.4,arg=0.1,putt=0.1")
    parser.add_argument("--ui",             action="store_true",
                        help="Launch interactive web UI for adjusting weights and running the model")
    args = parser.parse_args()

    # ── Simple sub-commands ───────────────────────────────────────────────────
    if args.ui:
        cmd_ui(args)
        return
    if args.config:
        cmd_config()
        return
    if args.league_setup:
        cmd_setup_league()
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
            total_w = sum(parts.values())
            if abs(total_w - 1.0) > 0.01:
                print(f"  [WARN] SG weights sum to {total_w:.2f}, not 1.0 — normalizing.")
                parts = {k: v / total_w for k, v in parts.items()}
            parts["type"] = "custom"
            sg_override = parts
        except Exception:
            print("  [ERROR] Invalid --sg-weights format. Use: ott=0.4,app=0.4,arg=0.1,putt=0.1")
            sys.exit(1)
    elif args.focus:
        sg_override = SG_FOCUS_PRESETS[args.focus]

    # ── Weekly picks run ──────────────────────────────────────────────────────
    print("\n  ⛳  Golf One-and-Done Picks Advisor  —  fetching data...\n")

    api_key = get_api_key()
    if not api_key:
        print("  ERROR: DataGolf API key is required.")
        print("  Run:  python golf_picks.py --config")
        sys.exit(1)

    league_cfg = load_league_cfg()
    my_team    = league_cfg.get("my_team", "")
    my_owner   = league_cfg.get("my_owner", "")

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
    t_name   = tournament.get("event_name", "")
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
    print(f"  → {used_count} players already used this season")

    # 9. MPSP league data
    print("  → Fetching league usage data from MPSP site...")
    usage_data = fetch_mpsp_golfer_usage(force=args.refresh)
    print(f"     {len(usage_data)} players with league usage data")

    print("  → Fetching current week pick data from MPSP site...")
    pick_data, picks_available = fetch_mpsp_current_picks(force=args.refresh)
    if picks_available:
        print(f"     {len(pick_data)} players with actual pick counts (deadline passed)")
    else:
        print("     Pick data not yet available — will estimate from win probability")

    print("  → Fetching league standings from MPSP site...")
    standings = fetch_mpsp_standings(force=args.refresh)
    year_count = len(standings.get("year", []))
    print(f"     {year_count} entries in year-long standings")

    # 10. Contest + strategy mode
    ev_contests = all_contests_for_event(t_name, sched, league_cfg)
    standings_ctx = my_standings_context(standings, my_team, my_owner) if (my_team or my_owner) else {}

    # Determine active contest (CLI override > event type > year)
    if args.contest:
        active_contest = args.contest
    elif tournament.get("is_major"):
        active_contest = "majors"
    elif any(kw in t_name.lower() for kw in COMMISSIONER_CUP_KEYWORDS):
        active_contest = "cup"
    else:
        active_contest = "year"

    # Determine strategy mode
    if args.mode != "auto":
        mode = args.mode
    elif standings_ctx and active_contest in standings_ctx:
        mode = standings_ctx[active_contest]["mode"]
    else:
        mode = "balanced"

    active_weights = get_weights_for_mode(mode)
    total_members  = detect_total_members(standings, usage_data,
                                          league_cfg.get("total_members", 0))
    mode_src = "manual override" if args.mode != "auto" else "auto from standings"
    print(f"     Strategy mode: {mode.upper()}  ({mode_src}, contest: {active_contest},"
          f" {total_members} league members)\n")

    # --show-standings early exit
    if args.show_standings:
        if not standings_ctx:
            print("  No standings data found. Run --league-setup to set your team name.")
        else:
            _print_contest_context(standings_ctx, ev_contests, active_contest, mode)
        print()
        return

    # 11. Score — first pass with balanced weights to estimate pick %
    print("  → Scoring eligible players...")
    scored_prelim = score_field(
        field=field,
        rankings=rankings,
        predictions=predictions,
        tournament=tournament,
        rem_schedule=rem,
        course_history=course_history,
        used_lower=used_lower,
        sg_override=sg_override,
        usage_data=usage_data,
        total_members=total_members,
        active_weights=get_weights_for_mode("balanced"),
        pick_data=pick_data if picks_available else None,
    )
    # Estimate pick % from win probs if deadline hasn't passed yet
    if not picks_available and scored_prelim:
        est_pcts = estimate_pick_pcts(scored_prelim, total_members)
    else:
        est_pcts = None

    # Score once per mode so user can choose
    scored_by_mode: dict = {}
    for mode_name in ["conservative", "balanced", "chase"]:
        scored_by_mode[mode_name] = score_field(
            field=field,
            rankings=rankings,
            predictions=predictions,
            tournament=tournament,
            rem_schedule=rem,
            course_history=course_history,
            used_lower=used_lower,
            sg_override=sg_override,
            usage_data=usage_data,
            total_members=total_members,
            active_weights=get_weights_for_mode(mode_name),
            pick_data=pick_data if picks_available else None,
            picks_estimated=est_pcts,
        )
    n_scored = len(scored_by_mode.get("balanced", []))
    print(f"     {n_scored} eligible players scored\n")

    if not n_scored:
        print("  No eligible players to recommend.")
        print("  (All players may be used, or data may be missing.)")
        sys.exit(0)

    # Generate reasons for union of top-5 across all modes
    seen_names: set = set()
    for mode_name in ["conservative", "balanced", "chase"]:
        for p in scored_by_mode[mode_name][:5]:
            if p["name"] not in seen_names:
                seen_names.add(p["name"])
                p["reason"] = generate_reason(p, tournament, rem)

    # 12. Print report
    print_report(
        tournament, scored_by_mode, used_count, rem,
        sg_profile=sg_override,
        standings_ctx=standings_ctx,
        ev_contests=ev_contests,
        active_contest=active_contest,
        auto_mode=mode,
        sched=sched,
        league_cfg=league_cfg,
    )


# ══════════════════════════════════════════════════════════════════════════════
# WEB UI  (python3 golf_picks.py --ui)
# ══════════════════════════════════════════════════════════════════════════════

_UI_STATE: dict = {}   # shared data between HTTP handler and scoring thread


def _ui_score(custom: dict) -> dict:
    """Re-score the field using custom SG + component weights. Returns top-5 per mode."""
    s = _UI_STATE
    # Normalize SG weights (user sliders may not sum to 1.0)
    sg_raw   = custom.get("sg", {})
    sg_total = sum(sg_raw.values()) or 1.0
    sg_profile = {k: v / sg_total for k, v in sg_raw.items()}
    sg_profile.setdefault("type", "custom")

    results = {}
    for mode_name in ("conservative", "balanced", "chase"):
        raw_w   = custom.get("weights", {}).get(mode_name, get_weights_for_mode(mode_name))
        w_total = sum(raw_w.values()) or 1.0
        weights = {k: v / w_total for k, v in raw_w.items()}

        scored = score_field(
            field=s["field"], rankings=s["rankings"], predictions=s["predictions"],
            tournament=s["tournament"], rem_schedule=s["rem"],
            course_history=s["course_history"], used_lower=s["used_lower"],
            sg_override=sg_profile, usage_data=s["usage_data"],
            total_members=s["total_members"],
            active_weights=weights,
            pick_data=s["pick_data"] if s["picks_available"] else None,
            picks_estimated=s["est_pcts"],
        )
        results[mode_name] = [
            {
                "name":        (p["name"].split(",")[1].strip() + " " + p["name"].split(",")[0]).title()
                               if "," in p["name"] else p["name"].title(),
                "final_score": round(p["final_score"], 1),
                "win_prob":    round(p.get("win_prob", 0), 1),
                "top10_prob":  round(p.get("top10_prob", 0), 1),
                "pick_pct":    round(p.get("pick_pct", 0), 1),
                "owgr":        p.get("owgr", 999),
                "is_elite":    p.get("is_elite", False),
                "lev_label":   pick_pct_label(p.get("pick_pct", 0)),
            }
            for p in scored[:8]
        ]
    return results


def _ui_baseline() -> dict:
    s = _UI_STATE
    course  = s["tournament"].get("course", "")
    profile = _course_profile(course)
    return {
        "sg": {k: profile[k] for k in ("sg_ott", "sg_app", "sg_arg", "sg_putt")},
        "weights": {
            "conservative": dict(WEIGHTS_CONSERVATIVE),
            "balanced":     dict(WEIGHTS_BALANCED),
            "chase":        dict(WEIGHTS_CHASE),
        },
    }


def _ui_render_html() -> bytes:
    s        = _UI_STATE
    t        = s["tournament"]
    baseline = _ui_baseline()
    profile  = _course_profile(t.get("course", ""))

    standings_parts = []
    for contest, ctx in s.get("standings_ctx", {}).items():
        lbl  = CONTEST_LABELS.get(contest, contest.upper())
        rank = ctx["rank"]; total = ctx["total"]
        g10  = ctx.get("gap_to_top10", 0)
        tag  = "✓ TOP 10" if ctx.get("in_top10") else f"${g10:,.0f} to top 10"
        standings_parts.append(f"{lbl}: #{rank}/{total} {tag}")
    standings_str = " &nbsp;·&nbsp; ".join(standings_parts) or "—"

    purse_m = f"${t.get('purse',0)/1e6:.1f}M" if t.get("purse") else "—"

    import json as _json
    baseline_js = _json.dumps(baseline)
    profile_type = profile.get("type", "balanced")

    html_path = Path(__file__).parent / "golf_picks_ui.html"
    template  = html_path.read_text() if html_path.exists() else _UI_HTML

    return (template
        .replace("__TOURNAMENT_NAME__", t.get("event_name", "Unknown"))
        .replace("__COURSE__",          t.get("course", ""))
        .replace("__PURSE__",           purse_m)
        .replace("__FIELD_SIZE__",      str(len(s.get("field", []))))
        .replace("__STANDINGS__",       standings_str)
        .replace("__PROFILE_TYPE__",    profile_type)
        .replace("__BASELINE_JSON__",   baseline_js)
    ).encode()


class _UIHandler:
    """Minimal HTTP request handler (no BaseHTTPRequestHandler subclass needed)."""
    pass


def cmd_ui(args):
    """Fetch data once, then serve the interactive weight-tuning UI at localhost:5051."""
    import threading
    import webbrowser
    import json as _json
    from http.server import HTTPServer, BaseHTTPRequestHandler

    # ── Fetch all data (same pipeline as main) ────────────────────────────────
    print("\n  ⛳  Golf One-and-Done Picks Advisor  —  loading UI data...\n")
    api_key = load_cfg().get("datagolf_api_key", "")
    if not api_key:
        print("  No API key. Run --config first.")
        return

    league_cfg    = load_league_cfg()
    my_team       = league_cfg.get("my_team", "")
    my_owner      = league_cfg.get("my_owner", "")

    sched         = fetch_schedule(api_key)
    tournament    = detect_tournament(sched, api_key)
    if not tournament:
        print("  Could not detect current tournament.")
        return
    t_name        = tournament.get("event_name", "")
    field         = fetch_field(api_key)
    rankings      = fetch_rankings(api_key)
    predictions   = fetch_predictions(api_key)
    event_id      = tournament.get("event_id")
    course_history= fetch_course_history(api_key, event_id) if event_id else {}
    rem           = remaining_schedule(sched, t_name)
    used_data     = load_used()
    used_lower    = used_names_set(used_data)
    usage_data    = fetch_mpsp_golfer_usage(force=args.refresh)
    pick_data, picks_available = fetch_mpsp_current_picks(force=args.refresh)
    standings     = fetch_mpsp_standings(force=args.refresh)
    ev_contests   = all_contests_for_event(t_name, sched, league_cfg)
    standings_ctx = my_standings_context(standings, my_team, my_owner) if (my_team or my_owner) else {}
    total_members = detect_total_members(standings, usage_data, league_cfg.get("total_members", 0))

    sg_override = SG_FOCUS_PRESETS.get(getattr(args, "focus", None) or "", None)

    # Prelim score for pick% estimation
    scored_prelim = score_field(
        field=field, rankings=rankings, predictions=predictions,
        tournament=tournament, rem_schedule=rem, course_history=course_history,
        used_lower=used_lower, sg_override=sg_override, usage_data=usage_data,
        total_members=total_members, active_weights=get_weights_for_mode("balanced"),
        pick_data=pick_data if picks_available else None,
    )
    est_pcts = estimate_pick_pcts(scored_prelim, total_members) if not picks_available else None

    _UI_STATE.update({
        "field": field, "rankings": rankings, "predictions": predictions,
        "tournament": tournament, "rem": rem, "course_history": course_history,
        "used_lower": used_lower, "usage_data": usage_data,
        "total_members": total_members, "pick_data": pick_data,
        "picks_available": picks_available, "est_pcts": est_pcts,
        "standings_ctx": standings_ctx,
    })

    # ── HTTP server ───────────────────────────────────────────────────────────
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *a): pass   # silence access log

        def do_GET(self):
            if self.path in ("/", "/index.html"):
                body = _ui_render_html()
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            else:
                self.send_response(404); self.end_headers()

        def do_POST(self):
            if self.path == "/run":
                length  = int(self.headers.get("Content-Length", 0))
                payload = _json.loads(self.rfile.read(length))
                result  = _ui_score(payload)
                body    = _json.dumps(result).encode()
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            else:
                self.send_response(404); self.end_headers()

    PORT   = 5051
    server = HTTPServer(("0.0.0.0", PORT), Handler)   # bind all interfaces (IPv4 + IPv6)
    url    = f"http://127.0.0.1:{PORT}"               # use explicit IP to avoid macOS IPv6 issue
    print(f"  Web UI ready →  {url}")
    print(f"  Serving {t_name}  |  {total_members} league members")
    print(f"  Press Ctrl+C to stop.\n")
    threading.Timer(0.6, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n  Web UI stopped.")


# ── Embedded HTML fallback (also written to golf_picks_ui.html on first run) ─
_UI_HTML = ""  # populated below — see golf_picks_ui.html


if __name__ == "__main__":
    main()


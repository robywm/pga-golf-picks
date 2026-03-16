#!/bin/bash
# run_golf.sh — One-click weekly golf picks launcher
# Double-click this file (or run it in Terminal) to get this week's picks.
# On Mondays the script auto-clears cache so you always see the current week.

set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo ""
echo "  ⛳  Golf One-and-Done Picks Advisor"
echo "  ────────────────────────────────────"
python3 "$DIR/golf_picks.py" --generate-html

echo ""
echo "  Opening picks in browser..."
open "$DIR/golf_picks.html"

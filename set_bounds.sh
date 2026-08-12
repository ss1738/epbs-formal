#!/usr/bin/env bash
# Set the id/slot bound of the TLA+ model.
#
# Apalache requires LITERAL constant ranges -- it rejects `0..MaxDepth` -- so the
# bound appears as a hardcoded integer in three places. This script keeps them in
# sync rather than leaving a reader to spot a mismatch, and makes every measured
# result reproducible by naming its bound instead of describing it in prose.
#
#   ./set_bounds.sh 4    # default: 5 blocks, enough for a competing fork
#   ./set_bounds.sh 2    # minimal: 3 blocks, enough for the P3 witness only
#
# WHY A SMALLER BOUND IS NOT FREE. nodeAnc ranges over [Ids -> SUBSET AncUniverse].
# At bound 4 that is 1024^5 ~ 1e15; at bound 2 it is 64^3 ~ 2.6e5. Ten orders of
# magnitude, and that term is what exhausts the rewriter heap. But at bound 2 the
# model holds only genesis + r + one child, so it CANNOT represent a competing
# fork alongside the payload branch. Bound 2 is adequate for hunting the P3
# tiebreak witness and is NOT a general-purpose reduction. Any result measured at
# bound 2 must be recorded with that bound stated.
set -euo pipefail

B="${1:?usage: set_bounds.sh <N>   (N = max block id / slot; 2 or 4)}"
cd "$(dirname "$0")"
F=specs/EPBSNodes.tla

python3 - "$B" "$F" <<'PY'
import re, sys, pathlib
b, f = sys.argv[1], pathlib.Path(sys.argv[2])
s = f.read_text()
s, n1 = re.subn(r"^Ids   == 0 \.\. \d+$",   f"Ids   == 0 .. {b}", s, flags=re.M)
s, n2 = re.subn(r"^Slots == 0 \.\. \d+$",   f"Slots == 0 .. {b}", s, flags=re.M)
s, n3 = re.subn(r"^ASSUME DepthOK == MaxDepth = \d+$",
                f"ASSUME DepthOK == MaxDepth = {b}", s, flags=re.M)
if (n1, n2, n3) != (1, 1, 1):
    sys.exit(f"expected one match each, got Ids={n1} Slots={n2} ASSUME={n3}")
f.write_text(s)
print(f"bound = {b}: Ids/Slots = 0..{b}, ASSUME DepthOK pinned to {b}")
PY

# The .cfg-free harnesses set MaxDepth in ConstInit; keep them in step or the
# ASSUME fails at parse time, which is the intended guard.
for MC in specs/MCEPBSNodes.tla specs/MCEPBSMultiSlotV2.tla; do
  [ -f "$MC" ] || continue
  python3 - "$B" "$MC" <<'PY'
import re, sys, pathlib
b, f = sys.argv[1], pathlib.Path(sys.argv[2])
s = f.read_text()
s2, n = re.subn(r"MaxDepth\s+= \d+", f"MaxDepth      = {b}", s)
if n:
    f.write_text(s2)
    print(f"  {f.name}: ConstInit MaxDepth = {b}")
PY
done

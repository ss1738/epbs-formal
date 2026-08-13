#!/usr/bin/env bash
# Every checkable operator in the active specs must appear in the probe registry
# (V2_VERIFICATION_SPEC.md section 2).
#
# WHY THIS EXISTS. A probe is DELIBERATELY FALSE: VIOLATED is its pass condition
# and HOLDS means the branch it guards is unreachable, which voids everything
# downstream. So an unregistered probe is worse than no probe -- a HOLDS reads as
# success either way, and nothing records which it should have been. A sweep on
# 2026-08-12 found 13 probes that no document mentioned. The registry closed that
# gap; this script stops it reopening.
#
# Run standalone or from verify.sh. Exits non-zero on an unregistered operator.
set -uo pipefail
cd "$(dirname "$0")"

REG=V2_VERIFICATION_SPEC.md
SPECS=(specs/EPBSNodes.tla specs/EPBSMultiSlotV2.tla)
missing=0

# Operators worth registering: probes (VAC_*, RVAC_*), invariants (S<digit>_*)
# and stated properties (P<digit>*) are detected by naming convention, which is
# why that convention exists. Operators that predate it -- TypeOK, AncClosure,
# AncRootsUnique -- are listed explicitly.
#
# Helpers are deliberately excluded: AncRoots and AncUniverse are a set-builder
# and a constant set, not checkable on their own. A greedy Anc[A-Za-z]+ pattern
# flagged both, which is why the list is explicit rather than a prefix match.
# NEW checkable operators should use a VAC_/RVAC_/S#_/P# name so they are caught
# automatically.
for f in "${SPECS[@]}"; do
  while read -r op; do
    [ -z "$op" ] && continue
    if ! grep -q "\`$op\`" "$REG"; then
      echo "  UNREGISTERED  $op   ($f)"
      missing=$((missing + 1))
    fi
  done < <(grep -oE '^(VAC_[A-Za-z0-9_]+|RVAC_[A-Za-z0-9_]+|S[0-9]_[A-Za-z0-9_]+|P[0-9][A-Za-z0-9_]*|TypeOK|AncClosure|AncRootsUnique|StructuralClosure)\b' "$f" \
           | sort -u)
done

# And the reverse: the registry must not cite operators that no longer exist.
stale=0
while read -r op; do
  [ -z "$op" ] && continue
  if ! grep -qE "^$op\b" "${SPECS[@]}"; then
    # Deliberately-deleted operators are exempt, but the exemption is bounded to
    # the "### Deleted" table itself. Using /,$p (to end of file) would silently
    # exempt anything added after it -- caught by a negative test.
    if sed -n '/^### Deleted/,/^## /p' "$REG" | grep -q "| \`$op\` |"; then continue; fi
    # (unregistered-direction check still scans the specs, which is correct)
    echo "  STALE IN REGISTRY  $op   (no longer defined)"
    stale=$((stale + 1))
  fi
# Scope to the section 2 registry TABLES only. Scanning the whole document
# flags design-only sketches elsewhere (section 6 names VAC_ParentPrevSlot,
# VAC_ParentWeak, VAC_TimelyEquivExists, none of which are implemented or
# claimed to be) as stale registry entries. Those are proposals, not records.
done < <(sed -n '/^## §2 Probe and invariant registry/,/^## §[^2]/p' "$REG" \
         | grep -oE '`(VAC_[A-Za-z0-9_]+|RVAC_[A-Za-z0-9_]+|S[0-9]_[A-Za-z0-9_]+|P[0-9][A-Za-z0-9_]*)`' \
         | tr -d '`' | sort -u)

if [ "$missing" -eq 0 ] && [ "$stale" -eq 0 ]; then
  echo "registry: OK — every checkable operator is registered, no stale entries"
  exit 0
fi
echo
echo "registry: $missing unregistered, $stale stale."
echo "Add missing operators to $REG section 2 with their EXPECTED outcome."
echo "For a probe the expected outcome is VIOLATED; HOLDS means it is dead."
exit 1

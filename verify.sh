#!/usr/bin/env bash
#
# Reproduce every claim in this repository with one command.
#
#   ./verify.sh
#
# Runs all TLA+ models under TLC (the safe ones must pass; the attack config
# must produce its expected reorg counterexample) and both Coq developments
# under coqc. Exits non-zero if anything is off.
#
# Requirements: Java (for TLC) and coqc (Coq / the Rocq Prover). The TLA+ tools
# jar is downloaded on first run, or point TLA2TOOLS at an existing copy.

set -uo pipefail
cd "$(dirname "$0")"

JAR="${TLA2TOOLS:-.cache/tla2tools.jar}"
if [ ! -f "$JAR" ]; then
  mkdir -p "$(dirname "$JAR")"
  echo "Fetching tla2tools.jar ..."
  curl -sL -o "$JAR" \
    https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
fi

fail=0

# TLC returns a non-zero exit code when it finds a violation, so we capture the
# output first and inspect it, rather than relying on the pipeline status.
tlc_green() { # name cfg tla
  printf "  TLC  %-24s " "$1"
  local out
  out="$(java -cp "$JAR" tlc2.TLC -config "specs/$2" "specs/$3" 2>&1)"
  if grep -q "No error has been found" <<<"$out"; then
    echo "PASS"
  else
    echo "FAIL"; fail=1
  fi
}

tlc_expect_violation() { # name cfg tla property
  printf "  TLC  %-24s " "$1"
  local out
  out="$(java -cp "$JAR" tlc2.TLC -config "specs/$2" "specs/$3" 2>&1)"
  if grep -q "$4 is violated" <<<"$out"; then
    echo "PASS (expected counterexample)"
  else
    echo "FAIL (expected $4 violation)"; fail=1
  fi
}

coq_check() { # file
  printf "  Coq  %-24s " "$1"
  if ( cd coq && coqc "$1" >/dev/null 2>&1 ); then echo "PASS"; else echo "FAIL"; fail=1; fi
}

echo "TLA+ models (TLC):"
tlc_green            "single-slot safety"  EPBS.cfg               EPBS.tla
tlc_green            "fork-choice (safe)"  EPBSForkChoice.cfg     EPBSForkChoice.tla
tlc_expect_violation "fork-choice (attack)" EPBSForkChoice_attack.cfg EPBSForkChoice.tla FC_TimelyPayloadSafe
tlc_green            "multi-slot chain"    EPBSChain.cfg          EPBSChain.tla
tlc_green            "timed PTC votes"     EPBSPTC.cfg            EPBSPTC.tla

echo "Coq proofs (coqc):"
coq_check EPBSPayment.v
coq_check EPBSForkChoice.v
coq_check EPBSEquivocation.v

echo
if [ "$fail" -eq 0 ]; then
  echo "ALL CHECKS PASSED"
else
  echo "SOME CHECKS FAILED"
fi
exit "$fail"

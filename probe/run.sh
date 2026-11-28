#!/bin/bash
# CI-only runner for the wip/rrv-probe branch (never part of the PR).
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS=4
M=CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.LinearStrongExtractor
F=CslibFrontier/Foundations/Combinatorics/AffineDisperser/Li/LinearStrongExtractor.lean
lake build --wfail --iofail $M CslibFrontierTests.LiLinearStrongExtractor > /tmp/b.log 2>&1; echo "BUILD_EXIT $?"
grep -v "^✔\|^Replayed\|^⣿" /tmp/b.log | tail -80
# axioms of the private csimp lemma and the public consumers: append to a copy, elaborate, restore
cp $F /tmp/orig.lean
printf '\n#print axioms Cslib.AffineDisperser.Li.rrvFunctions_eq_rrvFunctionsImpl\n#print axioms Cslib.AffineDisperser.Li.rrvWeakDesign\n#print axioms Cslib.AffineDisperser.Li.rrvWeakDesignTwo\n' >> $F
lake env lean $F 2>&1 | tail -12; echo "AXIOMS_EXIT $?"
cp /tmp/orig.lean $F
git diff --quiet && echo "tree clean after axioms"
run() { # name timeout evals...
  local name=$1 tmo=$2; shift 2
  local f=/tmp/probe_$name.lean
  cp probe/ProbeRRV.lean "$f"
  for e in "$@"; do printf '\n#eval %s\n' "$e" >> "$f"; done
  local t0=$(date +%s%N)
  timeout "$tmo" lake env lean "$f" 2>&1
  local code=$?
  echo "## group $name exit=$code wall_ms=$(( ($(date +%s%N) - t0) / 1000000 ))"
}
run tsweep 600 "row 1 2 3 true" "row 2 2 3 true" "row 3 2 3 true" "row 4 2 3 true"
run t5old 900 "row 5 2 3 true"
run tbig 600 "row 6 2 3 false" "row 8 2 3 false" "row 12 2 3 false" "row 16 2 3 false" "row 24 2 3 false" "row 32 2 3 false"
run msweep 600 "row 3 2 1 true" "row 3 2 2 true" "row 3 2 4 true" "row 3 2 5 true" "row 3 2 6 true"
run dsweep 600 "row 3 1 3 true" "row 3 3 3 true" "row 3 4 3 true"
run cheap 600 "row 32 2 0 true" "row 32 2 1 true" "row 32 1 8 true" "row 0 2 8 true" "row 1000 2 1 true"
run large 900 "row 8 16 8 false" "row 16 32 16 false" "row 32 2 32 false"

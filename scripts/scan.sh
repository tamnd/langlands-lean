#!/bin/sh
# Scan the main tree for the escape hatches of spec 09.2: sorry, admit, a new axiom, native_decide, implemented_by and @[extern]. Langlands/WIP is not scanned, because it is not imported by Langlands.lean. The script prints each hit and exits with code 1 when it finds one.
set -eu
hits=$(grep -rnE '\bsorry\b|\badmit\b|^[[:space:]]*(private |protected )?axiom |native_decide|implemented_by|@\[extern' Langlands Langlands.lean --include='*.lean' | grep -v '^Langlands/WIP/' | grep -vE ':[0-9]+:[[:space:]]*(--|/-|\*)' || true)
if [ -n "$hits" ]; then
  echo "$hits"
  echo "the main tree has an escape hatch; move the proof to Langlands/WIP"
  exit 1
fi
echo "the main tree has no escape hatch"

#!/usr/bin/env bash
# Verify mpverus. `--run` also compiles and runs the demo deployment.
set -uo pipefail

VERUS="${VERUS:-./tools/verus-arm64-macos/verus}"
if [ ! -x "$VERUS" ]; then
    cat >&2 <<MSG
Verus not found at: $VERUS

Install Verus (https://github.com/verus-lang/verus) and either put it at that
path or set VERUS to the binary:

    VERUS=/path/to/verus ./verify.sh
MSG
    exit 2
fi

status=0

echo "== the development =="
"$VERUS" src/main.rs --crate-type=bin || status=1

echo
echo "== counterexamples (each MUST be rejected) =="
bash counterexamples/check.sh || status=1

echo
echo "== spikes (design experiments, verified but not integrated) =="
for f in spike/*.rs; do
    out=$("$VERUS" "$f" --crate-type=bin 2>&1 | grep -o 'verification results.*')
    printf '  %-28s %s\n' "$f" "${out:-did not verify}"
done

if [ "${1:-}" = "--run" ]; then
    echo
    echo "== compile and run =="
    "$VERUS" src/main.rs --crate-type=bin --compile -o ./mpverus || status=1
    ./mpverus || status=1
fi

exit $status

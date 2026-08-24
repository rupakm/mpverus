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
# Spikes are design experiments, deliberately not integrated -- but they are
# cited as evidence in docs/plan.md, so a spike that stops verifying is a
# broken claim, not a curiosity. This loop used to print the verdict and drop
# it on the floor, so `verify.sh` reported success while a spike failed.
echo "== spikes (design experiments, verified but not integrated) =="
for f in spike/*.rs; do
    out=$("$VERUS" "$f" --crate-type=bin 2>&1) && rc=0 || rc=$?
    line=$(printf '%s' "$out" | grep -o 'verification results.*' | head -1)
    if [ "$rc" -ne 0 ] || [ -z "$line" ] || ! printf '%s' "$line" | grep -q ', 0 errors'; then
        printf '  %-28s FAILED\n' "$f"
        printf '%s\n' "$out" | grep -E '^error' | head -3 | sed 's/^/        /'
        status=1
    else
        printf '  %-28s %s\n' "$f" "$line"
    fi
done

if [ "${1:-}" = "--run" ]; then
    echo
    echo "== compile and run =="
    "$VERUS" src/main.rs --crate-type=bin --compile -o ./mpverus || status=1
    ./mpverus || status=1
fi

exit $status

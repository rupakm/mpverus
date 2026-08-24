set -u
VERUS="${VERUS:-./tools/verus-arm64-macos/verus}"
status=0

# Every file here MUST be rejected. It is not enough that Verus exits non-zero,
# since a typo would do that too and would silently turn this suite green while
# testing nothing. Each file therefore declares HOW it must fail:
#
#   "MUST FAIL TO VERIFY"  -- must reach verification with a non-zero error count
#   "MUST FAIL TO COMPILE" -- must NOT reach verification; the property is
#                             enforced by Rust's ownership rules, not the solver
#
# and may add "// EXPECT-ERROR: <regex>" to pin the specific diagnostic.
for f in counterexamples/*.rs; do
    out=$("$VERUS" "$f" --crate-type=bin --triggers-mode silent 2>&1)
    expect=$(sed -n 's|^// EXPECT-ERROR: ||p' "$f" | head -1)
    n=$(printf '%s' "$out" | sed -n 's/.*verification results:: [0-9]* verified, \([0-9]*\) errors.*/\1/p')

    if grep -q "MUST FAIL TO COMPILE" "$f"; then
        if [ -n "$n" ]; then
            echo "FAIL  $f reached verification, but must not compile"
            status=1
        elif [ -n "$expect" ] && ! printf '%s' "$out" | grep -qE "$expect"; then
            echo "FAIL  $f was rejected, but not with /$expect/"
            printf '%s\n' "$out" | grep -E '^error' | head -3 | sed 's/^/        /'
            status=1
        else
            echo "ok    $f rejected at compile time (${expect:-any error})"
        fi
    else
        if [ -z "$n" ]; then
            echo "FAIL  $f did not reach verification (compile error?)"
            printf '%s\n' "$out" | grep -E '^error' | head -3 | sed 's/^/        /'
            status=1
        elif [ "$n" -eq 0 ]; then
            echo "FAIL  $f verified, but it must not"
            status=1
        elif [ -n "$expect" ] && ! printf '%s' "$out" | grep -qE "$expect"; then
            echo "FAIL  $f failed verification, but not with /$expect/"
            status=1
        else
            echo "ok    $f rejected ($n verification errors)"
        fi
    fi
done
exit $status

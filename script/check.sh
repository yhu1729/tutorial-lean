#!/usr/bin/env bash
# Consistency checks for tutorial-lean. Runs `lake build` and inspects the result.
#
#   script/check.sh            # from anywhere inside the repository
#   LAKE="lake +leanprover/lean4:vX.Y.Z" script/check.sh   # with another toolchain
#
# Checks:
#   1. the build succeeds; the only warnings are `declaration uses `sorry`` inside
#      Exercise/; and no `info:` or `trace:` message comes from Tutorial/ or
#      Solution/ (every output-producing command there is under `#guard_msgs`,
#      which consumes its messages);
#   2. no `sorry` or `admit` in the code of Tutorial/ or Solution/ (comments and
#      backtick spans are stripped first; check 1 is the real guard, this one
#      catches a `sorry` that elaboration swallowed, e.g. under `#guard_msgs`);
#   3. every file in Tutorial/, Exercise/, Solution/ is imported by its root module;
#   4. each Exercise/E0N file and its Solution/S0N file declare the same names in
#      the same order, with the same signatures (text from the declaration keyword
#      to the first `:=`, `where`, or `|` alternative outside brackets, across lines; attributes such
#      as `@[simp]` are ignored, since adding one can be part of an exercise), and
#      every declaration that is given, i.e. contains no `sorry`, is identical in
#      both files;
#   5. every commented check block in an exercise file (consecutive `-- ` lines
#      containing a `#…` command, an `example`, or a `/--` docstring) is present,
#      uncommented and as consecutive lines, in the matching solution file;
#   6. every `#eval`/`#check`/`#print`/`#synth`/`#reduce` at column 0 in Tutorial/
#      and Solution/ is pinned by a preceding `#guard_msgs in` (optionally through
#      an `open X in` or `set_option … in` line); lines inside `/- … -/` comments
#      are skipped. Check 1 is the dynamic version of this check;
#   7. lessons 01-12 and their exercises and solutions import only this project,
#      `Init`, `Std`, and `Lean` (no Mathlib, and none of Mathlib's dependencies).
set -uo pipefail
cd "$(dirname "$0")/.."

LAKE="${LAKE:-lake}"
fail=0
err() { printf 'FAIL: %s\n' "$*"; fail=1; }

log="$(mktemp "${TMPDIR:-/tmp}/tutorial-lean-build.XXXXXX")" || exit 2
tmpd="$(mktemp -d "${TMPDIR:-/tmp}/tutorial-lean-check.XXXXXX")" || exit 2
trap 'rm -rf "$log" "$tmpd"' EXIT

# 1. Build and inspect the log.
if ! $LAKE build >"$log" 2>&1; then
  cat "$log"
  err "lake build failed"
fi
if grep -E '^warning:' "$log" | grep -vE "declaration uses .sorry." >/dev/null; then
  err "warnings other than 'declaration uses sorry':"
  grep -E '^warning:' "$log" | grep -vE "declaration uses .sorry."
fi
if grep -E '^warning:' "$log" | grep -E "declaration uses .sorry." | grep -v '^warning: Exercise/' >/dev/null; then
  err "'declaration uses sorry' outside Exercise/:"
  grep -E '^warning:' "$log" | grep -E "declaration uses .sorry." | grep -v '^warning: Exercise/'
fi
if grep -E '^(info|trace): [^ ]+\.lean:[0-9]+:[0-9]+:' "$log" | grep -v '^[a-z]*: Exercise/' >/dev/null; then
  err "unpinned output (info/trace message) outside Exercise/:"
  grep -E '^(info|trace): [^ ]+\.lean:[0-9]+:[0-9]+:' "$log" | grep -v '^[a-z]*: Exercise/'
fi
sorries=$(grep -cE "declaration uses .sorry." "$log" || true)

# Strip `/- … -/` comments (innermost first, so nesting works), `--` line comments,
# and backtick spans; print the remaining code with its original line numbers.
code() {
  perl -0777 -ne '
    1 while s{/-(?:(?!/-).)*?-/}{ my $m = $&; "\n" x ($m =~ tr/\n//) }gse;
    s/--[^\n]*//g;
    s/`[^`\n]*`//g;
    my $n = 0; print ++$n, ":", $_, "\n" for split /\n/, $_, -1;
  ' "$1"
}

# 2. No sorry or admit in the code of lessons and solutions.
for f in Tutorial/*.lean Solution/*.lean; do
  [ -e "$f" ] || continue
  if code "$f" | grep -nE '\b(sorry|admit)\b' >"$tmpd/sorry"; then
    err "sorry/admit in $f:"
    sed "s|^[0-9]*:|$f:|" "$tmpd/sorry"
  fi
done

# 3. Root modules import every file.
for lib in Tutorial Exercise Solution; do
  for f in "$lib"/*.lean; do
    [ -e "$f" ] || continue
    mod="$lib.$(basename "$f" .lean)"
    grep -qxF "import $mod" "$lib.lean" || err "$f is not imported by $lib.lean"
  done
done

# 4. Exercise and solution files declare the same things.
# `decls` prints one line per declaration: SIG<TAB>BLOCK, where SIG is the text
# from the keyword to the first `:=` or `where` at bracket depth 0 (whitespace
# normalised, attribute removed) and BLOCK is the whole declaration (its first line
# plus the indented lines that follow), with E0N/S0N replaced by X0N.
decls() {
  perl -pe 's/\b[ES]0(\d)\b/X0$1/g' "$1" | awk '
    function flush(   sig, i, c, depth, n, out) {
      if (block == "") return
      sig = block; sub(/^@\[[^]]*\][[:space:]]+/, "", sig)
      gsub(/\\n/, " ", sig); gsub(/[[:space:]]+/, " ", sig)
      n = length(sig); depth = 0; out = ""
      for (i = 1; i <= n; i++) {
        c = substr(sig, i, 1)
        if (c == "(" || c == "[" || c == "{") depth++
        else if (c == ")" || c == "]" || c == "}") depth--
        else if (depth == 0 && substr(sig, i, 2) == ":=") break
        else if (depth == 0 && substr(sig, i) ~ /^ where( |$)/) break
        else if (depth == 0 && substr(sig, i, 3) == " | ") break
        out = out c
      }
      sub(/[[:space:]]+$/, "", out)
      printf "%s\t%s\n", out, block
      block = ""
    }
    /^(@\[[^]]*\][[:space:]]+)?((private|protected|noncomputable|unsafe|partial)[[:space:]]+)*(def|theorem|instance|class|structure|inductive|abbrev|opaque)[[:space:]]/ {
      flush(); block = $0; next
    }
    block != "" && /^[[:space:]]+[^[:space:]]/ { block = block "\\n" $0; next }
    { flush() }
    END { flush() }' "$1"
}
for e in Exercise/E*.lean; do
  [ -e "$e" ] || continue
  n="$(basename "$e" .lean)"; s="Solution/S${n#E}.lean"
  if [ ! -f "$s" ]; then err "missing $s for $e"; continue; fi
  decls "$e" >"$tmpd/e.decl"; decls "$s" >"$tmpd/s.decl"
  cut -f1 "$tmpd/e.decl" >"$tmpd/e.sig"; cut -f1 "$tmpd/s.decl" >"$tmpd/s.sig"
  if ! diff "$tmpd/e.sig" "$tmpd/s.sig" >/dev/null; then
    err "declarations differ between $e and $s:"
    diff "$tmpd/e.sig" "$tmpd/s.sig" || true
  fi
  # Given declarations (no sorry) must be identical.
  cut -f2 "$tmpd/s.decl" >"$tmpd/s.block"
  grep -vE '\bsorry\b' "$tmpd/e.decl" | cut -f2 >"$tmpd/e.given"
  while IFS= read -r block; do
    grep -qxF -- "$block" "$tmpd/s.block" ||
      err "given declaration in $e differs in $s: ${block%%\\n*}"
  done <"$tmpd/e.given"
  # 5. Commented check blocks in E must be active, as consecutive lines, in S.
  { printf '\x1f'; perl -pe 's/\b[ES]0(\d)\b/X0$1/g' "$s" | tr '\n' '\037'; printf '\x1f'; } >"$tmpd/s.joined"
  perl -pe 's/\b[ES]0(\d)\b/X0$1/g' "$e" | awk '
    function flush() {
      if (blk != "" && ischeck) printf "\037%s\037\n", blk
      blk = ""; ischeck = 0
    }
    /^-- / || /^--$/ {
      line = substr($0, 4)
      if (line ~ /^(#|example |\/--)/) ischeck = 1
      blk = (blk == "" ? "" : blk "\037") line; next
    }
    { flush() }
    END { flush() }' >"$tmpd/e.checks"
  while IFS= read -r blk; do
    grep -qF -- "$blk" "$tmpd/s.joined" ||
      err "check block from $e is not active in $s: $(printf '%s' "$blk" | tr '\037' ' ' | cut -c1-70)"
  done <"$tmpd/e.checks"
done

# 6. Every output-producing command in a lesson or solution is pinned (static check).
for f in Tutorial/*.lean Solution/*.lean; do
  [ -e "$f" ] || continue
  unpinned="$(awk -v F="$f" '
    /^\/-/ && !/-\/[[:space:]]*$/ { incomment = 1 }
    incomment { if (/-\/[[:space:]]*$/) incomment = 0; prev2 = prev; prev = $0; next }
    /^(#eval|#check|#print|#synth|#reduce)([[:space:]]|$)/ {
      if (prev !~ /^#guard_msgs/ && !(prev ~ /^(open [A-Za-z0-9_.]+|set_option [^ ]+ [^ ]+) in$/ && prev2 ~ /^#guard_msgs/))
        printf "%s:%d: %s\n", F, NR, $0
    }
    { prev2 = prev; prev = $0 }' "$f")"
  if [ -n "$unpinned" ]; then
    err "command not under #guard_msgs in $f:"
    printf '%s\n' "$unpinned"
  fi
done

# 7. Parts I and II (lessons 01-12) use core Lean only.
for f in Tutorial/L0[1-9]_*.lean Tutorial/L1[0-2]_*.lean \
         Exercise/E0[1-9]_*.lean Exercise/E1[0-2]_*.lean \
         Solution/S0[1-9]_*.lean Solution/S1[0-2]_*.lean; do
  [ -e "$f" ] || continue
  if grep -nE '^import ' "$f" | grep -vE '^[0-9]+:import (Tutorial|Exercise|Solution|Init|Std|Lean)(\.|$)'; then
    err "$f imports outside core Lean; lessons 01-12 are core-only"
  fi
done

if [ "$fail" -eq 0 ]; then
  printf 'OK: build clean, %s exercise stubs still open\n' "$sorries"
fi
exit "$fail"

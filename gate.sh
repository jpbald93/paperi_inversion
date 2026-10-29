#!/bin/bash
# Gate for the Inversion Lean formalisation (planar inversion, Ptolemy, Peaucellier, Descartes/Soddy). Passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
#    `initialize`, `IO`, `set_option`, or syntax-extension commands (which could redefine
#    `#print axioms`);
#  * the library builds without errors;
#  * the gate itself generates the `#print axioms` report for each REQUIRED theorem;
#  * each REQUIRED theorem uses only Lean's standard axioms (propext, Classical.choice, Quot.sound).
# SCAFFOLD=1 skips the forbidden-token check and also tolerates `sorryAx`, so a partially
# finished development can be checked while it still contains `sorry`.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="Inversion"
LIB="Inversion"
REQUIRED="Inversion.invPt Inversion.invPt_zero Inversion.invPt_eq_inversion Inversion.norm_invPt Inversion.norm_sq_invPt Inversion.norm_mul_norm_invPt Inversion.invPt_ne_zero Inversion.invPt_invPt Inversion.inner_invPt Inversion.dist_sq_invPt Inversion.dist_invPt Inversion.inner_invPt_of_mem_circle Inversion.invPt_image_circle Inversion.ptolemy_iff_dist_add_dist_invPt Inversion.ptolemy_inequality Inversion.dist_add_dist_eq_iff_wbtw Inversion.collinear_iff_dist_boundary Inversion.inner_eq_re_im Inversion.exists_eq_smul_add Inversion.collinear_invPt_of_concyclic Inversion.ptolemy_concyclic Inversion.dist_sq_re_im Inversion.norm_sq_re_im Inversion.peaucellier_add Inversion.peaucellier_inner Inversion.peaucellier_collinear Inversion.peaucellier Inversion.peaucellier_classic Inversion.peaucellier_line Inversion.peaucellier_classic_line Inversion.descartesForm Inversion.descartes Inversion.dist_sq_fin3 Inversion.soddy Inversion.descartes_quadratic Inversion.descartes_solve Inversion.descartes_vieta Inversion.descartes_prod_eq Inversion.descartes_reflect Inversion.descartesFormZ Inversion.descartesFormZ_cast Inversion.apollonian_integral Inversion.apolloMove Inversion.IsDescartes Inversion.isDescartes_apolloMove Inversion.isDescartes_foldr"
SOURCES="$(ls Inversion/*.lean) Inversion.lean"
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if [ "${SCAFFOLD:-0}" != "1" ]; then
  if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
    echo "FAIL: forbidden token"; exit 1; fi
fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
if [ "${SCAFFOLD:-0}" = "1" ]; then ALLOW='^(propext|Classical\.choice|Quot\.sound|sorryAx)$'; else ALLOW='^(propext|Classical\.choice|Quot\.sound)$'; fi
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u | grep -vE "$ALLOW")
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"

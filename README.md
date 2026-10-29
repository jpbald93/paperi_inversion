# Inversion — planar inversion, Ptolemy, Peaucellier–Lipkin, Descartes/Soddy (Lean 4 + Mathlib)

Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; `.lake/packages` is a symlink to
`~/lean/paperi_arbelos/.lake/packages` (no fetch).

| File | Contents |
|---|---|
| `Inversion/Basic.lean` | `invPt R P = (R²/‖P‖²)•P`; `invPt_invPt` (involution), `norm_sq_invPt` (`‖P'‖² = R⁴/‖P‖²`), `dist_sq_invPt` (`dist(P',Q')² = R⁴ dist(P,Q)²/(‖P‖²‖Q‖²)`), `invPt_image_circle` (circle through `0` ↦ line), agreement with Mathlib's `EuclideanGeometry.inversion` |
| `Inversion/PtolemyInversion.lean` | `ptolemy_iff_dist_add_dist_invPt` (Ptolemy identity ⇔ `dist(P',Q') + dist(Q',S') = dist(P',S')`), `ptolemy_inequality`, `collinear_iff_dist_boundary`, `collinear_invPt_of_concyclic`, `ptolemy_concyclic` |
| `Inversion/Peaucellier.lean` | rhombus side `a`, connectors `b`: `peaucellier_inner` (`⟪P,Q⟫ = b² − a²`), `peaucellier` (`a² − b² = R²` ⇒ `Q = −invPt R P`, `‖P‖‖Q‖ = R²`), `peaucellier_classic` (`b² − a² = R²` ⇒ `Q = invPt R P`), `peaucellier_line`, `peaucellier_classic_line` (circle through pivot ↦ straight line) |
| `Inversion/Descartes.lean` | `descartes` (four tangent circles, signed radii), `soddy` (five tangent spheres in `ℝ³`, `(∑k)² = 3∑k²`), `descartes_solve` (`k₄ = k₁+k₂+k₃ ± 2√(k₁k₂+k₂k₃+k₃k₁)`), `descartes_vieta` (`k⁺+k⁻ = 2(k₁+k₂+k₃)`, `k⁺k⁻ = 2(k₁²+k₂²+k₃²) − (k₁+k₂+k₃)²`), `descartes_reflect`, `apollonian_integral`, `isDescartes_foldr` (integral Apollonian gaskets) |

Tangency convention for Descartes/Soddy: `dist(cᵢ,cⱼ)² = (rᵢ + rⱼ)²` with signed radii (an enclosing
circle has negative radius), `kᵢ = 1/rᵢ`. Proofs go through the vanishing Gram determinant of the
centre differences (3 vectors in `ℝ²`, resp. 4 vectors in `ℝ³`).

`bash gate.sh` — forbidden-token scan, build, `#print axioms` for every public declaration (standard
axioms only). `bash tests/tamper.sh` — 9 planted defects, each must be rejected.

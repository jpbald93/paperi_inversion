import Inversion.Peaucellier

/-!
# Descartes' circle theorem and Soddy's hexlet relation

Radii are *signed*: an enclosing circle gets a negative radius, so in every configuration of
pairwise tangent circles (externally tangent, or one enclosing the others) the tangency
conditions read `dist(cᵢ, cⱼ)² = (rᵢ + rⱼ)²`. With curvatures `kᵢ = 1 / rᵢ`:

* `descartes` : four pairwise tangent circles in the plane satisfy
  `(k₁ + k₂ + k₃ + k₄)² = 2 * (k₁² + k₂² + k₃² + k₄²)`;
* `soddy` : five pairwise tangent spheres in space satisfy `(∑ kᵢ)² = 3 * (∑ kᵢ²)`.

Both come from the vanishing of a Gram (Cayley–Menger) determinant: three vectors in `ℝ²`, resp.
four vectors in `ℝ³`, are linearly dependent.

The algebraic consequences: the two solutions `k₄⁺, k₄⁻` of the Descartes equation satisfy
`k₄⁺ + k₄⁻ = 2 * (k₁ + k₂ + k₃)` and `k₄⁺ * k₄⁻ = 2 * (k₁² + k₂² + k₃²) - (k₁ + k₂ + k₃)²`;
they are `k₁ + k₂ + k₃ ± 2 * √(k₁k₂ + k₂k₃ + k₃k₁)`, and the Apollonian move
`k₄ ↦ 2 * (k₁ + k₂ + k₃) - k₄` preserves both the Descartes relation and integrality.
-/

namespace Inversion

/-- The Descartes form `(∑ kᵢ)² - 2 ∑ kᵢ²`. -/
def descartesForm (k₁ k₂ k₃ k₄ : ℝ) : ℝ :=
  (k₁ + k₂ + k₃ + k₄) ^ 2 - 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2)

/-- Determinant of the symmetric matrix `[[a, b, c], [b, d, e], [c, e, f]]`. -/
private def det3 (a b c d e f : ℝ) : ℝ :=
  a * d * f + 2 * b * c * e - a * e ^ 2 - d * c ^ 2 - f * b ^ 2

/-- Dot product in coordinates of `ℝ³`. -/
private def dot (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Triple product (determinant) of three vectors of `ℝ³`. -/
private def triple (u v w : Fin 3 → ℝ) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- Determinant of a general `3 × 3` matrix, row by row. -/
private def det3g (a b c d e f g h i : ℝ) : ℝ :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- Determinant of a general `4 × 4` matrix (Laplace expansion along the first row). -/
private def det4g (g11 g12 g13 g14 g21 g22 g23 g24 g31 g32 g33 g34 g41 g42 g43 g44 : ℝ) : ℝ :=
  g11 * det3g g22 g23 g24 g32 g33 g34 g42 g43 g44 - g12 * det3g g21 g23 g24 g31 g33 g34 g41 g43 g44
    + g13 * det3g g21 g22 g24 g31 g32 g34 g41 g42 g44 - g14 * det3g g21 g22 g23 g31 g32 g33 g41 g42 g43

private theorem dot_comm (u v : Fin 3 → ℝ) : dot u v = dot v u := by unfold dot; ring

/-- Cauchy–Binet for `3 × 3` minors of a product. -/
private theorem det3g_dot (a b c p q r : Fin 3 → ℝ) :
    det3g (dot a p) (dot a q) (dot a r) (dot b p) (dot b q) (dot b r) (dot c p) (dot c q) (dot c r)
      = triple a b c * triple p q r := by
  unfold det3g dot triple; ring

/-- Four vectors of `ℝ³` are linearly dependent, with the triple products as coefficients. -/
private theorem triple_dep (v₁ v₂ v₃ v₄ : Fin 3 → ℝ) (k : Fin 3) :
    triple v₂ v₃ v₄ * v₁ k - triple v₁ v₃ v₄ * v₂ k + triple v₁ v₂ v₄ * v₃ k
      - triple v₁ v₂ v₃ * v₄ k = 0 := by
  unfold triple; fin_cases k <;> simp <;> ring

/-- The Gram determinant of four vectors of `ℝ³` vanishes. -/
private theorem gram4_eq_zero (v₁ v₂ v₃ v₄ : Fin 3 → ℝ) :
    det4g (dot v₁ v₁) (dot v₁ v₂) (dot v₁ v₃) (dot v₁ v₄) (dot v₂ v₁) (dot v₂ v₂) (dot v₂ v₃)
      (dot v₂ v₄) (dot v₃ v₁) (dot v₃ v₂) (dot v₃ v₃) (dot v₃ v₄) (dot v₄ v₁) (dot v₄ v₂)
      (dot v₄ v₃) (dot v₄ v₄) = 0 := by
  unfold det4g
  rw [det3g_dot, det3g_dot, det3g_dot, det3g_dot]
  simp only [dot]
  linear_combination triple v₂ v₃ v₄ * (v₁ 0 * triple_dep v₁ v₂ v₃ v₄ 0
    + v₁ 1 * triple_dep v₁ v₂ v₃ v₄ 1 + v₁ 2 * triple_dep v₁ v₂ v₃ v₄ 2)

/-- **Descartes' circle theorem.** Four pairwise tangent circles with signed radii `rᵢ ≠ 0`
(tangency: `dist(cᵢ, cⱼ)² = (rᵢ + rⱼ)²`). -/
theorem descartes {c₁ c₂ c₃ c₄ : ℂ} {r₁ r₂ r₃ r₄ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0)
    (h₄ : r₄ ≠ 0) (h₁₂ : dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2) (h₁₃ : dist c₁ c₃ ^ 2 = (r₁ + r₃) ^ 2)
    (h₁₄ : dist c₁ c₄ ^ 2 = (r₁ + r₄) ^ 2) (h₂₃ : dist c₂ c₃ ^ 2 = (r₂ + r₃) ^ 2)
    (h₂₄ : dist c₂ c₄ ^ 2 = (r₂ + r₄) ^ 2) (h₃₄ : dist c₃ c₄ ^ 2 = (r₃ + r₄) ^ 2) :
    (1 / r₁ + 1 / r₂ + 1 / r₃ + 1 / r₄) ^ 2 =
      2 * ((1 / r₁) ^ 2 + (1 / r₂) ^ 2 + (1 / r₃) ^ 2 + (1 / r₄) ^ 2) := by
  simp only [dist_sq_re_im] at h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄
  set x₁ := c₁.re - c₄.re; set y₁ := c₁.im - c₄.im
  set x₂ := c₂.re - c₄.re; set y₂ := c₂.im - c₄.im
  set x₃ := c₃.re - c₄.re; set y₃ := c₃.im - c₄.im
  have g11 : x₁ * x₁ + y₁ * y₁ = (r₁ + r₄) ^ 2 := by linear_combination h₁₄
  have g22 : x₂ * x₂ + y₂ * y₂ = (r₂ + r₄) ^ 2 := by linear_combination h₂₄
  have g33 : x₃ * x₃ + y₃ * y₃ = (r₃ + r₄) ^ 2 := by linear_combination h₃₄
  have g12 : x₁ * x₂ + y₁ * y₂ = ((r₁ + r₄) ^ 2 + (r₂ + r₄) ^ 2 - (r₁ + r₂) ^ 2) / 2 := by
    linear_combination (1/2 : ℝ) * h₁₄ + (1/2 : ℝ) * h₂₄ - (1/2 : ℝ) * h₁₂
  have g13 : x₁ * x₃ + y₁ * y₃ = ((r₁ + r₄) ^ 2 + (r₃ + r₄) ^ 2 - (r₁ + r₃) ^ 2) / 2 := by
    linear_combination (1/2 : ℝ) * h₁₄ + (1/2 : ℝ) * h₃₄ - (1/2 : ℝ) * h₁₃
  have g23 : x₂ * x₃ + y₂ * y₃ = ((r₂ + r₄) ^ 2 + (r₃ + r₄) ^ 2 - (r₂ + r₃) ^ 2) / 2 := by
    linear_combination (1/2 : ℝ) * h₂₄ + (1/2 : ℝ) * h₃₄ - (1/2 : ℝ) * h₂₃
  -- three vectors in the plane: the Gram determinant vanishes
  have h0 : det3 (x₁ * x₁ + y₁ * y₁) (x₁ * x₂ + y₁ * y₂) (x₁ * x₃ + y₁ * y₃) (x₂ * x₂ + y₂ * y₂)
      (x₂ * x₃ + y₂ * y₃) (x₃ * x₃ + y₃ * y₃) = 0 := by unfold det3; ring
  rw [g11, g12, g13, g22, g23, g33] at h0
  unfold det3 at h0
  field_simp
  linear_combination (1/4 : ℝ) * h0

/-- Coordinates of a point of `ℝ³`. -/
theorem dist_sq_fin3 (x y : EuclideanSpace ℝ (Fin 3)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.dist_eq, sq_abs]

/-- **Soddy's five-sphere relation.** Five pairwise tangent spheres in `ℝ³` with signed radii
`rᵢ ≠ 0` satisfy `(∑ kᵢ)² = 3 * (∑ kᵢ²)`. -/
theorem soddy {c₁ c₂ c₃ c₄ c₅ : EuclideanSpace ℝ (Fin 3)} {r₁ r₂ r₃ r₄ r₅ : ℝ} (h₁ : r₁ ≠ 0)
    (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0) (h₄ : r₄ ≠ 0) (h₅ : r₅ ≠ 0)
    (h₁₂ : dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2) (h₁₃ : dist c₁ c₃ ^ 2 = (r₁ + r₃) ^ 2)
    (h₁₄ : dist c₁ c₄ ^ 2 = (r₁ + r₄) ^ 2) (h₁₅ : dist c₁ c₅ ^ 2 = (r₁ + r₅) ^ 2)
    (h₂₃ : dist c₂ c₃ ^ 2 = (r₂ + r₃) ^ 2) (h₂₄ : dist c₂ c₄ ^ 2 = (r₂ + r₄) ^ 2)
    (h₂₅ : dist c₂ c₅ ^ 2 = (r₂ + r₅) ^ 2) (h₃₄ : dist c₃ c₄ ^ 2 = (r₃ + r₄) ^ 2)
    (h₃₅ : dist c₃ c₅ ^ 2 = (r₃ + r₅) ^ 2) (h₄₅ : dist c₄ c₅ ^ 2 = (r₄ + r₅) ^ 2) :
    (1 / r₁ + 1 / r₂ + 1 / r₃ + 1 / r₄ + 1 / r₅) ^ 2 =
      3 * ((1 / r₁) ^ 2 + (1 / r₂) ^ 2 + (1 / r₃) ^ 2 + (1 / r₄) ^ 2 + (1 / r₅) ^ 2) := by
  simp only [dist_sq_fin3] at h₁₂ h₁₃ h₁₄ h₁₅ h₂₃ h₂₄ h₂₅ h₃₄ h₃₅ h₄₅
  let v₁ : Fin 3 → ℝ := fun k ↦ c₁ k - c₅ k
  let v₂ : Fin 3 → ℝ := fun k ↦ c₂ k - c₅ k
  let v₃ : Fin 3 → ℝ := fun k ↦ c₃ k - c₅ k
  let v₄ : Fin 3 → ℝ := fun k ↦ c₄ k - c₅ k
  have h0 := gram4_eq_zero v₁ v₂ v₃ v₄
  rw [dot_comm v₂ v₁, dot_comm v₃ v₁, dot_comm v₄ v₁, dot_comm v₃ v₂,
    dot_comm v₄ v₂, dot_comm v₄ v₃] at h0
  have g11 : dot v₁ v₁ = (r₁ + r₅) ^ 2 := by
    simp only [dot, v₁]
    linear_combination h₁₅
  have g12 : dot v₁ v₂ = ((r₁ + r₅) ^ 2 + (r₂ + r₅) ^ 2 - (r₁ + r₂) ^ 2) / 2 := by
    simp only [dot, v₁, v₂]
    linear_combination (1/2 : ℝ) * h₁₅ + (1/2 : ℝ) * h₂₅ - (1/2 : ℝ) * h₁₂
  have g13 : dot v₁ v₃ = ((r₁ + r₅) ^ 2 + (r₃ + r₅) ^ 2 - (r₁ + r₃) ^ 2) / 2 := by
    simp only [dot, v₁, v₃]
    linear_combination (1/2 : ℝ) * h₁₅ + (1/2 : ℝ) * h₃₅ - (1/2 : ℝ) * h₁₃
  have g14 : dot v₁ v₄ = ((r₁ + r₅) ^ 2 + (r₄ + r₅) ^ 2 - (r₁ + r₄) ^ 2) / 2 := by
    simp only [dot, v₁, v₄]
    linear_combination (1/2 : ℝ) * h₁₅ + (1/2 : ℝ) * h₄₅ - (1/2 : ℝ) * h₁₄
  have g22 : dot v₂ v₂ = (r₂ + r₅) ^ 2 := by
    simp only [dot, v₂]
    linear_combination h₂₅
  have g23 : dot v₂ v₃ = ((r₂ + r₅) ^ 2 + (r₃ + r₅) ^ 2 - (r₂ + r₃) ^ 2) / 2 := by
    simp only [dot, v₂, v₃]
    linear_combination (1/2 : ℝ) * h₂₅ + (1/2 : ℝ) * h₃₅ - (1/2 : ℝ) * h₂₃
  have g24 : dot v₂ v₄ = ((r₂ + r₅) ^ 2 + (r₄ + r₅) ^ 2 - (r₂ + r₄) ^ 2) / 2 := by
    simp only [dot, v₂, v₄]
    linear_combination (1/2 : ℝ) * h₂₅ + (1/2 : ℝ) * h₄₅ - (1/2 : ℝ) * h₂₄
  have g33 : dot v₃ v₃ = (r₃ + r₅) ^ 2 := by
    simp only [dot, v₃]
    linear_combination h₃₅
  have g34 : dot v₃ v₄ = ((r₃ + r₅) ^ 2 + (r₄ + r₅) ^ 2 - (r₃ + r₄) ^ 2) / 2 := by
    simp only [dot, v₃, v₄]
    linear_combination (1/2 : ℝ) * h₃₅ + (1/2 : ℝ) * h₄₅ - (1/2 : ℝ) * h₃₄
  have g44 : dot v₄ v₄ = (r₄ + r₅) ^ 2 := by
    simp only [dot, v₄]
    linear_combination h₄₅
  rw [g11, g12, g13, g14, g22, g23, g24, g33, g34, g44] at h0
  unfold det4g det3g at h0
  field_simp
  linear_combination (1/8 : ℝ) * h0

/-- The Descartes relation as a quadratic equation in `k₄`. -/
theorem descartes_quadratic (k₁ k₂ k₃ k₄ : ℝ) :
    descartesForm k₁ k₂ k₃ k₄ = 0 ↔
      k₄ ^ 2 - 2 * (k₁ + k₂ + k₃) * k₄ + (2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) - (k₁ + k₂ + k₃) ^ 2) = 0 := by
  unfold descartesForm
  constructor <;> intro h <;> linear_combination -h

/-- **Quadratic solution formula.** The solutions of the Descartes equation in `k₄` are exactly
`k₁ + k₂ + k₃ ± 2 * √(k₁k₂ + k₂k₃ + k₃k₁)`; in particular the discriminant is nonnegative. -/
theorem descartes_solve (k₁ k₂ k₃ k₄ : ℝ) :
    descartesForm k₁ k₂ k₃ k₄ = 0 ↔ 0 ≤ k₁ * k₂ + k₂ * k₃ + k₃ * k₁ ∧
      (k₄ = k₁ + k₂ + k₃ + 2 * √(k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ∨
        k₄ = k₁ + k₂ + k₃ - 2 * √(k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) := by
  have e : descartesForm k₁ k₂ k₃ k₄ =
      4 * (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) - (k₄ - (k₁ + k₂ + k₃)) ^ 2 := by
    unfold descartesForm; ring
  rw [e]
  constructor
  · intro h
    have hq : 0 ≤ k₁ * k₂ + k₂ * k₃ + k₃ * k₁ := by nlinarith [sq_nonneg (k₄ - (k₁ + k₂ + k₃))]
    refine ⟨hq, ?_⟩
    have hs := Real.sq_sqrt hq
    have : (k₄ - (k₁ + k₂ + k₃) - 2 * √(k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) *
        (k₄ - (k₁ + k₂ + k₃) + 2 * √(k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) = 0 := by
      linear_combination (-1 : ℝ) * h - 4 * hs
    rcases mul_eq_zero.1 this with h' | h'
    · left; linarith
    · right; linarith
  · rintro ⟨hq, h | h⟩ <;> rw [h] <;> linear_combination (-4 : ℝ) * Real.sq_sqrt hq

/-- **Vieta for the two Descartes solutions.** If `k₄⁺ ≠ k₄⁻` both complete `k₁, k₂, k₃`
to a Descartes quadruple, then `k₄⁺ + k₄⁻ = 2 (k₁ + k₂ + k₃)` and
`k₄⁺ k₄⁻ = 2 (k₁² + k₂² + k₃²) - (k₁ + k₂ + k₃)²`. -/
theorem descartes_vieta {k₁ k₂ k₃ kp km : ℝ} (hp : descartesForm k₁ k₂ k₃ kp = 0)
    (hm : descartesForm k₁ k₂ k₃ km = 0) (hne : kp ≠ km) :
    kp + km = 2 * (k₁ + k₂ + k₃) ∧
      kp * km = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) - (k₁ + k₂ + k₃) ^ 2 := by
  rw [descartes_quadratic] at hp hm
  have hs : kp + km = 2 * (k₁ + k₂ + k₃) := by
    have : (kp - km) * (kp + km - 2 * (k₁ + k₂ + k₃)) = 0 := by linear_combination hp - hm
    linarith [(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)]
  refine ⟨hs, ?_⟩
  have hkm : km = 2 * (k₁ + k₂ + k₃) - kp := by linarith
  rw [hkm]
  linear_combination -hp

/-- The product of the two solutions in symmetric-function form. -/
theorem descartes_prod_eq (k₁ k₂ k₃ : ℝ) :
    2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) - (k₁ + k₂ + k₃) ^ 2 =
      k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 - 2 * (k₁ * k₂ + k₂ * k₃ + k₃ * k₁) := by ring

/-- The Apollonian move: the second solution `2 (k₁ + k₂ + k₃) - k₄` is again a Descartes
quadruple. -/
theorem descartes_reflect {k₁ k₂ k₃ k₄ : ℝ} (h : descartesForm k₁ k₂ k₃ k₄ = 0) :
    descartesForm k₁ k₂ k₃ (2 * (k₁ + k₂ + k₃) - k₄) = 0 := by
  unfold descartesForm at *; linear_combination h

/-- The Descartes form over `ℤ`. -/
def descartesFormZ (k₁ k₂ k₃ k₄ : ℤ) : ℤ :=
  (k₁ + k₂ + k₃ + k₄) ^ 2 - 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2)

theorem descartesFormZ_cast (k₁ k₂ k₃ k₄ : ℤ) :
    (descartesFormZ k₁ k₂ k₃ k₄ : ℝ) = descartesForm k₁ k₂ k₃ k₄ := by
  unfold descartesFormZ descartesForm; push_cast; ring

/-- **Integral Apollonian gaskets.** If `k₁, k₂, k₃, k₄` are integers satisfying the Descartes
relation, then so is the reflected quadruple with `k₄' = 2 (k₁ + k₂ + k₃) - k₄`; in
particular `k₄'` is an integer curvature, so every circle of the gasket has integral
curvature. -/
theorem apollonian_integral {k₁ k₂ k₃ k₄ : ℤ} (h : descartesFormZ k₁ k₂ k₃ k₄ = 0) :
    descartesFormZ k₁ k₂ k₃ (2 * (k₁ + k₂ + k₃) - k₄) = 0 ∧
      ((2 * (k₁ + k₂ + k₃) - k₄ : ℤ) : ℝ) = 2 * ((k₁ : ℝ) + k₂ + k₃) - k₄ := by
  refine ⟨?_, by push_cast; ring⟩
  unfold descartesFormZ at *; linear_combination h

/-- The four Apollonian moves on a quadruple of integer curvatures. -/
def apolloMove : Fin 4 → ℤ × ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℤ
  | 0, (a, b, c, d) => (2 * (b + c + d) - a, b, c, d)
  | 1, (a, b, c, d) => (a, 2 * (a + c + d) - b, c, d)
  | 2, (a, b, c, d) => (a, b, 2 * (a + b + d) - c, d)
  | 3, (a, b, c, d) => (a, b, c, 2 * (a + b + c) - d)

/-- A quadruple satisfies the Descartes relation. -/
def IsDescartes (q : ℤ × ℤ × ℤ × ℤ) : Prop := descartesFormZ q.1 q.2.1 q.2.2.1 q.2.2.2 = 0

theorem isDescartes_apolloMove (i : Fin 4) {q : ℤ × ℤ × ℤ × ℤ} (h : IsDescartes q) :
    IsDescartes (apolloMove i q) := by
  obtain ⟨a, b, c, d⟩ := q
  unfold IsDescartes descartesFormZ at *
  fin_cases i <;> simp only [apolloMove] <;> linear_combination h

/-- Every quadruple reachable from a Descartes quadruple by Apollonian moves is again an
integral Descartes quadruple. -/
theorem isDescartes_foldr (l : List (Fin 4)) {q : ℤ × ℤ × ℤ × ℤ} (h : IsDescartes q) :
    IsDescartes (l.foldr apolloMove q) := by
  induction l with
  | nil => exact h
  | cons i l ih => exact isDescartes_apolloMove i ih

/-- The classical `(-1, 2, 2, 3)` gasket: the move on the last curvature gives `15`. -/
example : apolloMove 3 (-1, 2, 2, 3) = (-1, 2, 2, 3) ∧ IsDescartes (-1, 2, 2, 3) ∧
    apolloMove 0 (-1, 2, 2, 3) = (15, 2, 2, 3) :=
  ⟨rfl, by unfold IsDescartes descartesFormZ; norm_num, rfl⟩

end Inversion

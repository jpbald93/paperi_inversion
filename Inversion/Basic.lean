import Mathlib

/-!
# Inversion in a circle centred at the origin

For a real inner product space `V` (in the applications `V = ℂ`, the Euclidean plane) and a
radius `R`, the inversion `invPt R` sends `P ≠ 0` to the point `(R² / ‖P‖²) • P` on the ray
`0P` with `‖P‖ * ‖invPt R P‖ = R²`; it fixes `0` by convention.

Main results:
* `invPt_invPt` : inversion is an involution (for `R ≠ 0`);
* `norm_sq_invPt` : `‖invPt R P‖² = R⁴ / ‖P‖²` (radial scaling);
* `dist_sq_invPt` : the chord-length distortion formula
  `dist(P', Q')² = R⁴ * dist(P, Q)² / (‖P‖² * ‖Q‖²)`;
* `invPt_image_circle` : a circle through the origin (origin removed) is mapped onto a line.
-/

namespace Inversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Inversion in the circle of radius `R` centred at the origin (`0` is sent to `0`). -/
noncomputable def invPt (R : ℝ) (P : V) : V := (R ^ 2 / ‖P‖ ^ 2) • P

theorem invPt_zero (R : ℝ) : invPt R (0 : V) = 0 := by simp [invPt]

/-- `invPt` agrees with Mathlib's `EuclideanGeometry.inversion` centred at `0`. -/
theorem invPt_eq_inversion (R : ℝ) (P : V) : invPt R P = EuclideanGeometry.inversion 0 R P := by
  simp [invPt, EuclideanGeometry.inversion, div_pow]

theorem norm_invPt (R : ℝ) (P : V) : ‖invPt R P‖ = R ^ 2 / ‖P‖ := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp [invPt]
  have h : 0 < ‖P‖ := norm_pos_iff.2 hP
  rw [invPt, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

/-- **Radial scaling.** -/
theorem norm_sq_invPt (R : ℝ) (P : V) : ‖invPt R P‖ ^ 2 = R ^ 4 / ‖P‖ ^ 2 := by
  rw [norm_invPt]; ring

theorem norm_mul_norm_invPt (R : ℝ) {P : V} (hP : P ≠ 0) : ‖P‖ * ‖invPt R P‖ = R ^ 2 := by
  have h : 0 < ‖P‖ := norm_pos_iff.2 hP
  rw [norm_invPt]; field_simp

theorem invPt_ne_zero {R : ℝ} (hR : R ≠ 0) {P : V} (hP : P ≠ 0) : invPt R P ≠ 0 :=
  smul_ne_zero (div_ne_zero (pow_ne_zero 2 hR) (pow_ne_zero 2 (norm_ne_zero_iff.2 hP))) hP

/-- **Inversion is an involution.** -/
theorem invPt_invPt {R : ℝ} (hR : R ≠ 0) (P : V) : invPt R (invPt R P) = P := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp [invPt]
  have h : 0 < ‖P‖ := norm_pos_iff.2 hP
  rw [invPt, norm_sq_invPt, invPt, smul_smul]
  conv_rhs => rw [← one_smul ℝ P]
  congr 1
  field_simp

theorem inner_invPt (R : ℝ) (P Q : V) :
    inner ℝ (invPt R P) (invPt R Q) = R ^ 4 * inner ℝ P Q / (‖P‖ ^ 2 * ‖Q‖ ^ 2) := by
  simp only [invPt, real_inner_smul_left, real_inner_smul_right]
  ring

/-- **Chord-length distortion formula.** -/
theorem dist_sq_invPt (R : ℝ) {P Q : V} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    dist (invPt R P) (invPt R Q) ^ 2 = R ^ 4 * dist P Q ^ 2 / (‖P‖ ^ 2 * ‖Q‖ ^ 2) := by
  have hp : 0 < ‖P‖ := norm_pos_iff.2 hP
  have hq : 0 < ‖Q‖ := norm_pos_iff.2 hQ
  rw [dist_eq_norm, dist_eq_norm, norm_sub_sq_real, norm_sub_sq_real, norm_sq_invPt,
    norm_sq_invPt, inner_invPt]
  field_simp
  ring

theorem dist_invPt (R : ℝ) {P Q : V} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    dist (invPt R P) (invPt R Q) = R ^ 2 * dist P Q / (‖P‖ * ‖Q‖) := by
  have hp : 0 < ‖P‖ := norm_pos_iff.2 hP
  have hq : 0 < ‖Q‖ := norm_pos_iff.2 hQ
  rw [← pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero, dist_sq_invPt R hP hQ]
  ring

/-- A point of the circle through the origin with centre `C` is sent to the line
`⟪Y, C⟫ = R² / 2`. -/
theorem inner_invPt_of_mem_circle (R : ℝ) {C P : V} (hP : P ≠ 0) (h : ‖P - C‖ = ‖C‖) :
    inner ℝ (invPt R P) C = R ^ 2 / 2 := by
  have hp : 0 < ‖P‖ := norm_pos_iff.2 hP
  have h2 : ‖P - C‖ ^ 2 = ‖C‖ ^ 2 := by rw [h]
  rw [norm_sub_sq_real] at h2
  rw [invPt, real_inner_smul_left]
  field_simp
  linear_combination (-R ^ 2) * h2

/-- **A circle through the centre of inversion is mapped onto a line.** -/
theorem invPt_image_circle {R : ℝ} (hR : R ≠ 0) (C : V) :
    invPt R '' {P | ‖P - C‖ = ‖C‖ ∧ P ≠ 0} = {Y | inner ℝ Y C = R ^ 2 / 2} := by
  ext Y
  constructor
  · rintro ⟨P, ⟨hPC, hP⟩, rfl⟩
    exact inner_invPt_of_mem_circle R hP hPC
  · intro hY
    have hY' : inner ℝ Y C = R ^ 2 / 2 := hY
    have hY0 : Y ≠ 0 := by
      rintro rfl
      simp at hY'
      exact hR (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
    have hy : 0 < ‖Y‖ := norm_pos_iff.2 hY0
    refine ⟨invPt R Y, ⟨?_, invPt_ne_zero hR hY0⟩, invPt_invPt hR Y⟩
    rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_sub_sq_real,
      norm_sq_invPt]
    rw [invPt, real_inner_smul_left, hY']
    field_simp
    ring

end Inversion

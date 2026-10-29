import Inversion.PtolemyInversion

/-!
# The Peaucellier–Lipkin linkage

The pivot `O = 0` is joined by two connectors of length `b` to the joints `A ≠ B`; the joints
`P ≠ Q` complete a rhombus `P A Q B` of side `a`. Then `O, P, Q` lie on the perpendicular
bisector of `AB` and `⟪P, Q⟫ = b² - a²` (`peaucellier_inner`). Hence:

* with `a² - b² = R²` (the pivot lies inside the rhombus, between `P` and `Q`),
  `‖P‖ * ‖Q‖ = R²` and `Q = -invPt R P`;
* with `b² - a² = R²` (the classical cell, pivot outside the rhombus), `Q = invPt R P`.

In both cases, when `P` runs on a circle through `O`, the point `Q` runs on a straight line.
-/

namespace Inversion

theorem dist_sq_re_im (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]; simp; ring

theorem norm_sq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- In the plane, a vector orthogonal to both `w ≠ 0` and `v ≠ 0`, with `v ⊥ w`, vanishes. -/
private theorem eq_zero_of_orth {w1 w2 v1 v2 z1 z2 : ℝ} (hw : w1 ≠ 0 ∨ w2 ≠ 0)
    (hv : v1 ≠ 0 ∨ v2 ≠ 0) (hzw : z1 * w1 + z2 * w2 = 0) (hvw : v1 * w1 + v2 * w2 = 0)
    (hzv : z1 * v1 + z2 * v2 = 0) : z1 = 0 ∧ z2 = 0 := by
  have hc : z1 * v2 - z2 * v1 = 0 := by
    rcases hw with hw | hw
    · exact (mul_eq_zero.1 (show w1 * (z1 * v2 - z2 * v1) = 0 by
        linear_combination v2 * hzw - z2 * hvw)).resolve_left hw
    · exact (mul_eq_zero.1 (show w2 * (z1 * v2 - z2 * v1) = 0 by
        linear_combination z1 * hvw - v1 * hzw)).resolve_left hw
  have hn : (z1 ^ 2 + z2 ^ 2) * (v1 ^ 2 + v2 ^ 2) = 0 := by
    linear_combination (z1 * v1 + z2 * v2) * hzv + (z1 * v2 - z2 * v1) * hc
  have hvn : v1 ^ 2 + v2 ^ 2 ≠ 0 := by
    rcases hv with hv | hv <;> positivity
  have hz := (mul_eq_zero.1 hn).resolve_right hvn
  constructor <;> nlinarith [sq_nonneg z1, sq_nonneg z2]

private theorem re_im_ne {z w : ℂ} (h : z ≠ w) : z.re - w.re ≠ 0 ∨ z.im - w.im ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (Complex.ext (by linarith [hc.1]) (by linarith [hc.2]))

section Linkage

variable {a b : ℝ} {A B P Q : ℂ}

/-- The two rhombus vertices `P, Q` are symmetric about the midpoint of `AB`. -/
theorem peaucellier_add (hA : ‖A‖ = b) (hB : ‖B‖ = b) (hPA : dist P A = a) (hPB : dist P B = a)
    (hQA : dist Q A = a) (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q) : P + Q = A + B := by
  have eA := congrArg (· ^ 2) hA; have eB := congrArg (· ^ 2) hB
  have ePA := congrArg (· ^ 2) hPA; have ePB := congrArg (· ^ 2) hPB
  have eQA := congrArg (· ^ 2) hQA; have eQB := congrArg (· ^ 2) hQB
  simp only [norm_sq_re_im, dist_sq_re_im] at eA eB ePA ePB eQA eQB
  obtain ⟨h1, h2⟩ := eq_zero_of_orth (re_im_ne hAB) (re_im_ne hPQ)
    (z1 := P.re + Q.re - A.re - B.re) (z2 := P.im + Q.im - A.im - B.im)
    (by linear_combination (-1/2 : ℝ) * ePA + (1/2 : ℝ) * ePB - (1/2 : ℝ) * eQA + (1/2 : ℝ) * eQB)
    (by linear_combination (-1/2 : ℝ) * ePA + (1/2 : ℝ) * ePB + (1/2 : ℝ) * eQA - (1/2 : ℝ) * eQB)
    (by linear_combination (1/2 : ℝ) * ePA + (1/2 : ℝ) * ePB - (1/2 : ℝ) * eQA - (1/2 : ℝ) * eQB)
  apply Complex.ext <;> simp <;> linarith

/-- **Peaucellier–Lipkin cell.** `⟪P, Q⟫ = b² - a²`. -/
theorem peaucellier_inner (hA : ‖A‖ = b) (hB : ‖B‖ = b) (hPA : dist P A = a)
    (hPB : dist P B = a) (hQA : dist Q A = a) (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q) :
    inner ℝ P Q = b ^ 2 - a ^ 2 := by
  have hs := peaucellier_add hA hB hPA hPB hQA hQB hAB hPQ
  have hre : P.re + Q.re = A.re + B.re := by simpa using congrArg Complex.re hs
  have him : P.im + Q.im = A.im + B.im := by simpa using congrArg Complex.im hs
  have eA := congrArg (· ^ 2) hA; have eB := congrArg (· ^ 2) hB
  have ePA := congrArg (· ^ 2) hPA; have eQA := congrArg (· ^ 2) hQA
  simp only [norm_sq_re_im, dist_sq_re_im] at eA eB ePA eQA
  rw [inner_eq_re_im]
  have hQre : Q.re = A.re + B.re - P.re := by linarith
  have hQim : Q.im = A.im + B.im - P.im := by linarith
  rw [hQre, hQim] at eQA ⊢
  linear_combination (-1/2 : ℝ) * ePA - (1/2 : ℝ) * eQA + (1/2 : ℝ) * eA + (1/2 : ℝ) * eB

/-- `O, P, Q` are collinear. -/
theorem peaucellier_collinear (hA : ‖A‖ = b) (hB : ‖B‖ = b) (hPA : dist P A = a)
    (hPB : dist P B = a) (hQA : dist Q A = a) (hQB : dist Q B = a) (hAB : A ≠ B) :
    P.re * Q.im - P.im * Q.re = 0 := by
  have eA := congrArg (· ^ 2) hA; have eB := congrArg (· ^ 2) hB
  have ePA := congrArg (· ^ 2) hPA; have ePB := congrArg (· ^ 2) hPB
  have eQA := congrArg (· ^ 2) hQA; have eQB := congrArg (· ^ 2) hQB
  simp only [norm_sq_re_im, dist_sq_re_im] at eA eB ePA ePB eQA eQB
  have hP : P.re * (A.re - B.re) + P.im * (A.im - B.im) = 0 := by
    linear_combination (-1/2 : ℝ) * ePA + (1/2 : ℝ) * ePB + (1/2 : ℝ) * eA - (1/2 : ℝ) * eB
  have hQ : Q.re * (A.re - B.re) + Q.im * (A.im - B.im) = 0 := by
    linear_combination (-1/2 : ℝ) * eQA + (1/2 : ℝ) * eQB + (1/2 : ℝ) * eA - (1/2 : ℝ) * eB
  rcases re_im_ne hAB with hw | hw
  · exact (mul_eq_zero.1 (show (A.re - B.re) * (P.re * Q.im - P.im * Q.re) = 0 by
      linear_combination Q.im * hP - P.im * hQ)).resolve_left hw
  · exact (mul_eq_zero.1 (show (A.im - B.im) * (P.re * Q.im - P.im * Q.re) = 0 by
      linear_combination P.re * hQ - Q.re * hP)).resolve_left hw

/-- A point collinear with `O` and `P ≠ 0` is a multiple of `P`. -/
private theorem eq_smul_of_cross {P Q : ℂ} (hP : P ≠ 0) (h : P.re * Q.im - P.im * Q.re = 0) :
    Q = (inner ℝ P Q / ‖P‖ ^ 2) • P := by
  have hn : P.re ^ 2 + P.im ^ 2 ≠ 0 := by
    rw [← norm_sq_re_im]; positivity
  rw [inner_eq_re_im, norm_sq_re_im]
  apply Complex.ext <;> simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> field_simp
  · linear_combination (-P.im) * h
  · linear_combination P.re * h

/-- **Peaucellier–Lipkin linkage, `a² - b² = R²`.** The linkage enforces `‖P‖ * ‖Q‖ = R²`; in
fact `Q = -invPt R P` (the pivot lies between `P` and `Q`). -/
theorem peaucellier {R : ℝ} (hR : R ≠ 0) (hab : a ^ 2 - b ^ 2 = R ^ 2) (hA : ‖A‖ = b)
    (hB : ‖B‖ = b) (hPA : dist P A = a) (hPB : dist P B = a) (hQA : dist Q A = a)
    (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q) :
    Q = -invPt R P ∧ ‖P‖ * ‖Q‖ = R ^ 2 := by
  have hi := peaucellier_inner hA hB hPA hPB hQA hQB hAB hPQ
  have hP : P ≠ 0 := by
    rintro rfl
    simp at hi
    exact hR (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
  have hQ : Q = -invPt R P := by
    rw [eq_smul_of_cross hP (peaucellier_collinear hA hB hPA hPB hQA hQB hAB), hi, invPt,
      ← neg_smul]
    congr 1
    linear_combination (-1 / ‖P‖ ^ 2) * hab
  refine ⟨hQ, ?_⟩
  rw [hQ, norm_neg, norm_mul_norm_invPt R hP]

/-- **Classical Peaucellier cell, `b² - a² = R²`.** Here `Q = invPt R P`. -/
theorem peaucellier_classic {R : ℝ} (hR : R ≠ 0) (hab : b ^ 2 - a ^ 2 = R ^ 2) (hA : ‖A‖ = b)
    (hB : ‖B‖ = b) (hPA : dist P A = a) (hPB : dist P B = a) (hQA : dist Q A = a)
    (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q) :
    Q = invPt R P ∧ ‖P‖ * ‖Q‖ = R ^ 2 := by
  have hi := peaucellier_inner hA hB hPA hPB hQA hQB hAB hPQ
  have hP : P ≠ 0 := by
    rintro rfl
    simp at hi
    exact hR (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
  have hQ : Q = invPt R P := by
    rw [eq_smul_of_cross hP (peaucellier_collinear hA hB hPA hPB hQA hQB hAB), hi, invPt, hab]
  exact ⟨hQ, hQ ▸ norm_mul_norm_invPt R hP⟩

/-- **Straight-line motion.** If `P` is constrained to a circle through the pivot with centre
`C`, then `Q` moves on the straight line `⟪Q, C⟫ = -R² / 2`. -/
theorem peaucellier_line {R : ℝ} {C : ℂ} (hR : R ≠ 0) (hab : a ^ 2 - b ^ 2 = R ^ 2)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b) (hPA : dist P A = a) (hPB : dist P B = a) (hQA : dist Q A = a)
    (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q) (hPC : ‖P - C‖ = ‖C‖) :
    inner ℝ Q C = -(R ^ 2 / 2) := by
  obtain ⟨hQ, hPQn⟩ := peaucellier hR hab hA hB hPA hPB hQA hQB hAB hPQ
  have hP : P ≠ 0 := by rintro rfl; simp at hPQn; exact hR (pow_eq_zero_iff two_ne_zero |>.1 hPQn.symm)
  rw [hQ, inner_neg_left, inner_invPt_of_mem_circle R hP hPC]

/-- **Straight-line motion, classical cell.** `Q` moves on the line `⟪Q, C⟫ = R² / 2`. -/
theorem peaucellier_classic_line {R : ℝ} {C : ℂ} (hR : R ≠ 0) (hab : b ^ 2 - a ^ 2 = R ^ 2)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b) (hPA : dist P A = a) (hPB : dist P B = a) (hQA : dist Q A = a)
    (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q) (hPC : ‖P - C‖ = ‖C‖) :
    inner ℝ Q C = R ^ 2 / 2 := by
  obtain ⟨hQ, hPQn⟩ := peaucellier_classic hR hab hA hB hPA hPB hQA hQB hAB hPQ
  have hP : P ≠ 0 := by rintro rfl; simp at hPQn; exact hR (pow_eq_zero_iff two_ne_zero |>.1 hPQn.symm)
  rw [hQ, inner_invPt_of_mem_circle R hP hPC]

end Linkage

end Inversion

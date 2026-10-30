import Inversion.Descartes

/-!
# Layer 14: Mathlib-only restatements and explicit witnesses

`l14_<name>` restates each main theorem with the local definitions unfolded: the inversion
`invPt R` is replaced by Mathlib's `EuclideanGeometry.inversion 0 R` (they agree,
`invPt_eq_inversion`), and `descartesForm` by its defining polynomial. Each is proved from the
library theorem.

`l14w_<name>` gives a concrete configuration satisfying every hypothesis, with a non-degenerate
conclusion.
-/

open EuclideanGeometry

namespace Inversion

section Restatements

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Inversion is an involution. -/
theorem l14_invPt_invPt {R : ℝ} (hR : R ≠ 0) (P : V) :
    inversion (0 : V) R (inversion (0 : V) R P) = P := by
  simpa only [invPt_eq_inversion] using invPt_invPt hR P

/-- Radial scaling of inversion. -/
theorem l14_norm_sq_invPt (R : ℝ) (P : V) :
    ‖inversion (0 : V) R P‖ ^ 2 = R ^ 4 / ‖P‖ ^ 2 := by
  simpa only [invPt_eq_inversion] using norm_sq_invPt R P

/-- Distortion of distances under inversion. -/
theorem l14_dist_sq_invPt (R : ℝ) {P Q : V} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    dist (inversion (0 : V) R P) (inversion (0 : V) R Q) ^ 2 =
      R ^ 4 * dist P Q ^ 2 / (‖P‖ ^ 2 * ‖Q‖ ^ 2) := by
  simpa only [invPt_eq_inversion] using dist_sq_invPt R hP hQ

/-- A circle through the centre (centre removed) is mapped onto a line. -/
theorem l14_invPt_image_circle {R : ℝ} (hR : R ≠ 0) (C : V) :
    inversion (0 : V) R '' {P | ‖P - C‖ = ‖C‖ ∧ P ≠ 0} = {Y | inner ℝ Y C = R ^ 2 / 2} := by
  have : inversion (0 : V) R = invPt R := funext fun P => (invPt_eq_inversion R P).symm
  rw [this]; exact invPt_image_circle hR C

/-- **Ptolemy via inversion**: Ptolemy's identity for `0, P, Q, S` is equivalent to the
collinear-betweenness equality of the images. -/
theorem l14_ptolemy_iff_dist_add_dist_invPt {R : ℝ} (hR : R ≠ 0) {P Q S : V} (hP : P ≠ 0)
    (hQ : Q ≠ 0) (hS : S ≠ 0) :
    dist (inversion (0 : V) R P) (inversion (0 : V) R Q) +
        dist (inversion (0 : V) R Q) (inversion (0 : V) R S) =
      dist (inversion (0 : V) R P) (inversion (0 : V) R S) ↔
      dist P Q * ‖S‖ + dist Q S * ‖P‖ = dist P S * ‖Q‖ := by
  simpa only [invPt_eq_inversion] using ptolemy_iff_dist_add_dist_invPt hR hP hQ hS

/-- **Ptolemy's inequality.** -/
theorem l14_ptolemy_inequality {P Q S : V} (hP : P ≠ 0) (hQ : Q ≠ 0) (hS : S ≠ 0) :
    dist P S * ‖Q‖ ≤ dist P Q * ‖S‖ + dist Q S * ‖P‖ :=
  ptolemy_inequality hP hQ hS

/-- Inversion maps three further points of a circle through `0` to collinear points. -/
theorem l14_collinear_invPt_of_concyclic {R : ℝ} {K P Q S : ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hS : S ≠ 0) (hPK : ‖P - K‖ = ‖K‖) (hQK : ‖Q - K‖ = ‖K‖) (hSK : ‖S - K‖ = ‖K‖) :
    Collinear ℝ ({inversion (0 : ℂ) R P, inversion (0 : ℂ) R Q, inversion (0 : ℂ) R S} : Set ℂ) := by
  simpa only [invPt_eq_inversion] using collinear_invPt_of_concyclic (R := R) hP hQ hS hPK hQK hSK

/-- **Ptolemy's theorem** for four concyclic points `0, P, Q, S`. -/
theorem l14_ptolemy_concyclic {K P Q S : ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) (hS : S ≠ 0)
    (hPK : ‖P - K‖ = ‖K‖) (hQK : ‖Q - K‖ = ‖K‖) (hSK : ‖S - K‖ = ‖K‖) :
    dist P Q * ‖S‖ + dist Q S * ‖P‖ = dist P S * ‖Q‖ ∨
      dist Q S * ‖P‖ + dist S P * ‖Q‖ = dist Q P * ‖S‖ ∨
        dist S P * ‖Q‖ + dist P Q * ‖S‖ = dist S Q * ‖P‖ :=
  ptolemy_concyclic hP hQ hS hPK hQK hSK

/-- **Peaucellier–Lipkin** (pivot inside the rhombus). -/
theorem l14_peaucellier {a b R : ℝ} {A B P Q : ℂ} (hR : R ≠ 0) (hab : a ^ 2 - b ^ 2 = R ^ 2)
    (hA : ‖A‖ = b) (hB : ‖B‖ = b) (hPA : dist P A = a) (hPB : dist P B = a) (hQA : dist Q A = a)
    (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q) :
    Q = -inversion (0 : ℂ) R P ∧ ‖P‖ * ‖Q‖ = R ^ 2 := by
  simpa only [invPt_eq_inversion] using peaucellier hR hab hA hB hPA hPB hQA hQB hAB hPQ

/-- **Peaucellier–Lipkin** (classical cell). -/
theorem l14_peaucellier_classic {a b R : ℝ} {A B P Q : ℂ} (hR : R ≠ 0)
    (hab : b ^ 2 - a ^ 2 = R ^ 2) (hA : ‖A‖ = b) (hB : ‖B‖ = b) (hPA : dist P A = a)
    (hPB : dist P B = a) (hQA : dist Q A = a) (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q) :
    Q = inversion (0 : ℂ) R P ∧ ‖P‖ * ‖Q‖ = R ^ 2 := by
  simpa only [invPt_eq_inversion] using peaucellier_classic hR hab hA hB hPA hPB hQA hQB hAB hPQ

/-- The classical cell turns a circle through the pivot into a straight line. -/
theorem l14_peaucellier_classic_line {a b R : ℝ} {A B P Q C : ℂ} (hR : R ≠ 0)
    (hab : b ^ 2 - a ^ 2 = R ^ 2) (hA : ‖A‖ = b) (hB : ‖B‖ = b) (hPA : dist P A = a)
    (hPB : dist P B = a) (hQA : dist Q A = a) (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q)
    (hPC : ‖P - C‖ = ‖C‖) :
    inner ℝ Q C = R ^ 2 / 2 :=
  peaucellier_classic_line hR hab hA hB hPA hPB hQA hQB hAB hPQ hPC

theorem l14_peaucellier_line {a b R : ℝ} {A B P Q C : ℂ} (hR : R ≠ 0)
    (hab : a ^ 2 - b ^ 2 = R ^ 2) (hA : ‖A‖ = b) (hB : ‖B‖ = b) (hPA : dist P A = a)
    (hPB : dist P B = a) (hQA : dist Q A = a) (hQB : dist Q B = a) (hAB : A ≠ B) (hPQ : P ≠ Q)
    (hPC : ‖P - C‖ = ‖C‖) :
    inner ℝ Q C = -(R ^ 2 / 2) :=
  peaucellier_line hR hab hA hB hPA hPB hQA hQB hAB hPQ hPC

end Restatements

/-- **Descartes' circle theorem.** -/
theorem l14_descartes {c₁ c₂ c₃ c₄ : ℂ} {r₁ r₂ r₃ r₄ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (h₃ : r₃ ≠ 0) (h₄ : r₄ ≠ 0) (h₁₂ : dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2)
    (h₁₃ : dist c₁ c₃ ^ 2 = (r₁ + r₃) ^ 2) (h₁₄ : dist c₁ c₄ ^ 2 = (r₁ + r₄) ^ 2)
    (h₂₃ : dist c₂ c₃ ^ 2 = (r₂ + r₃) ^ 2) (h₂₄ : dist c₂ c₄ ^ 2 = (r₂ + r₄) ^ 2)
    (h₃₄ : dist c₃ c₄ ^ 2 = (r₃ + r₄) ^ 2) :
    (1 / r₁ + 1 / r₂ + 1 / r₃ + 1 / r₄) ^ 2 =
      2 * ((1 / r₁) ^ 2 + (1 / r₂) ^ 2 + (1 / r₃) ^ 2 + (1 / r₄) ^ 2) :=
  descartes h₁ h₂ h₃ h₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄

/-- **Soddy's five-sphere relation.** -/
theorem l14_soddy {c₁ c₂ c₃ c₄ c₅ : EuclideanSpace ℝ (Fin 3)} {r₁ r₂ r₃ r₄ r₅ : ℝ} (h₁ : r₁ ≠ 0)
    (h₂ : r₂ ≠ 0) (h₃ : r₃ ≠ 0) (h₄ : r₄ ≠ 0) (h₅ : r₅ ≠ 0)
    (h₁₂ : dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2) (h₁₃ : dist c₁ c₃ ^ 2 = (r₁ + r₃) ^ 2)
    (h₁₄ : dist c₁ c₄ ^ 2 = (r₁ + r₄) ^ 2) (h₁₅ : dist c₁ c₅ ^ 2 = (r₁ + r₅) ^ 2)
    (h₂₃ : dist c₂ c₃ ^ 2 = (r₂ + r₃) ^ 2) (h₂₄ : dist c₂ c₄ ^ 2 = (r₂ + r₄) ^ 2)
    (h₂₅ : dist c₂ c₅ ^ 2 = (r₂ + r₅) ^ 2) (h₃₄ : dist c₃ c₄ ^ 2 = (r₃ + r₄) ^ 2)
    (h₃₅ : dist c₃ c₅ ^ 2 = (r₃ + r₅) ^ 2) (h₄₅ : dist c₄ c₅ ^ 2 = (r₄ + r₅) ^ 2) :
    (1 / r₁ + 1 / r₂ + 1 / r₃ + 1 / r₄ + 1 / r₅) ^ 2 =
      3 * ((1 / r₁) ^ 2 + (1 / r₂) ^ 2 + (1 / r₃) ^ 2 + (1 / r₄) ^ 2 + (1 / r₅) ^ 2) :=
  soddy h₁ h₂ h₃ h₄ h₅ h₁₂ h₁₃ h₁₄ h₁₅ h₂₃ h₂₄ h₂₅ h₃₄ h₃₅ h₄₅

/-- Solving the Descartes relation for the fourth curvature. -/
theorem l14_descartes_solve (k₁ k₂ k₃ k₄ : ℝ) :
    (k₁ + k₂ + k₃ + k₄) ^ 2 - 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2) = 0 ↔
      0 ≤ k₁ * k₂ + k₂ * k₃ + k₃ * k₁ ∧
      (k₄ = k₁ + k₂ + k₃ + 2 * √(k₁ * k₂ + k₂ * k₃ + k₃ * k₁) ∨
        k₄ = k₁ + k₂ + k₃ - 2 * √(k₁ * k₂ + k₂ * k₃ + k₃ * k₁)) :=
  descartes_solve k₁ k₂ k₃ k₄

/-- Vieta for the two solutions of the Descartes relation. -/
theorem l14_descartes_vieta {k₁ k₂ k₃ kp km : ℝ}
    (hp : (k₁ + k₂ + k₃ + kp) ^ 2 - 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + kp ^ 2) = 0)
    (hm : (k₁ + k₂ + k₃ + km) ^ 2 - 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + km ^ 2) = 0) (hne : kp ≠ km) :
    kp + km = 2 * (k₁ + k₂ + k₃) ∧
      kp * km = 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) - (k₁ + k₂ + k₃) ^ 2 :=
  descartes_vieta hp hm hne

/-- Integral Apollonian gaskets: the reflected curvature is again an integral solution. -/
theorem l14_apollonian_integral {k₁ k₂ k₃ k₄ : ℤ}
    (h : (k₁ + k₂ + k₃ + k₄) ^ 2 - 2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + k₄ ^ 2) = 0) :
    (k₁ + k₂ + k₃ + (2 * (k₁ + k₂ + k₃) - k₄)) ^ 2 -
        2 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 + (2 * (k₁ + k₂ + k₃) - k₄) ^ 2) = 0 ∧
      ((2 * (k₁ + k₂ + k₃) - k₄ : ℤ) : ℝ) = 2 * ((k₁ : ℝ) + k₂ + k₃) - k₄ :=
  apollonian_integral h

/-! ### Witnesses -/

section Witnesses

theorem l14h_dist {z w : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = d ^ 2) : dist z w = d := by
  rw [Complex.dist_eq_re_im, h, Real.sqrt_sq hd]

theorem l14h_norm {z : ℂ} {d : ℝ} (hd : 0 ≤ d) (h : z.re ^ 2 + z.im ^ 2 = d ^ 2) : ‖z‖ = d := by
  rw [← dist_zero_right]; exact l14h_dist hd (by simpa using h)

/-- **Witness for Descartes.** Curvatures `(-1, 2, 2, 3)`: the unit circle (enclosing, radius
`-1`), circles of radius `1/2` about `±1/2`, and the circle of radius `1/3` about `2i/3`; all six
tangency conditions hold and both sides equal `36`. -/
theorem l14w_descartes :
    let c₁ : ℂ := 0; let c₂ : ℂ := ⟨1 / 2, 0⟩; let c₃ : ℂ := ⟨-1 / 2, 0⟩; let c₄ : ℂ := ⟨0, 2 / 3⟩
    let r₁ : ℝ := -1; let r₂ : ℝ := 1 / 2; let r₃ : ℝ := 1 / 2; let r₄ : ℝ := 1 / 3
    r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ r₃ ≠ 0 ∧ r₄ ≠ 0 ∧
    dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2 ∧ dist c₁ c₃ ^ 2 = (r₁ + r₃) ^ 2 ∧
    dist c₁ c₄ ^ 2 = (r₁ + r₄) ^ 2 ∧ dist c₂ c₃ ^ 2 = (r₂ + r₃) ^ 2 ∧
    dist c₂ c₄ ^ 2 = (r₂ + r₄) ^ 2 ∧ dist c₃ c₄ ^ 2 = (r₃ + r₄) ^ 2 ∧
    (1 / r₁, 1 / r₂, 1 / r₃, 1 / r₄) = ((-1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ)) ∧
    (1 / r₁ + 1 / r₂ + 1 / r₃ + 1 / r₄) ^ 2 = 36 ∧
    2 * ((1 / r₁) ^ 2 + (1 / r₂) ^ 2 + (1 / r₃) ^ 2 + (1 / r₄) ^ 2) = 36 := by
  intro c₁ c₂ c₃ c₄ r₁ r₂ r₃ r₄
  refine ⟨by norm_num [r₁], by norm_num [r₂], by norm_num [r₃], by norm_num [r₄], ?_, ?_, ?_, ?_,
    ?_, ?_, by norm_num [r₁, r₂, r₃, r₄], by norm_num [r₁, r₂, r₃, r₄],
    by norm_num [r₁, r₂, r₃, r₄]⟩ <;>
  · rw [dist_sq_re_im]; norm_num [c₁, c₂, c₃, c₄, r₁, r₂, r₃, r₄]

/-- **Witness for Soddy.** Five pairwise tangent spheres in `ℝ³`: the unit sphere (radius `-1`),
spheres of radius `1/2` about `(±1/2, 0, 0)`, and spheres of radius `1/3` about
`(0, 1/√3, ±1/3)`. Curvatures `(-1, 2, 2, 3, 3)`, both sides equal `81`. -/
theorem l14w_soddy :
    let c₁ : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 0]
    let c₂ : EuclideanSpace ℝ (Fin 3) := !₂[1 / 2, 0, 0]
    let c₃ : EuclideanSpace ℝ (Fin 3) := !₂[-1 / 2, 0, 0]
    let c₄ : EuclideanSpace ℝ (Fin 3) := !₂[0, 1 / √3, 1 / 3]
    let c₅ : EuclideanSpace ℝ (Fin 3) := !₂[0, 1 / √3, -1 / 3]
    let r₁ : ℝ := -1; let r₂ : ℝ := 1 / 2; let r₃ : ℝ := 1 / 2; let r₄ : ℝ := 1 / 3
    let r₅ : ℝ := 1 / 3
    r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ r₃ ≠ 0 ∧ r₄ ≠ 0 ∧ r₅ ≠ 0 ∧
    dist c₁ c₂ ^ 2 = (r₁ + r₂) ^ 2 ∧ dist c₁ c₃ ^ 2 = (r₁ + r₃) ^ 2 ∧
    dist c₁ c₄ ^ 2 = (r₁ + r₄) ^ 2 ∧ dist c₁ c₅ ^ 2 = (r₁ + r₅) ^ 2 ∧
    dist c₂ c₃ ^ 2 = (r₂ + r₃) ^ 2 ∧ dist c₂ c₄ ^ 2 = (r₂ + r₄) ^ 2 ∧
    dist c₂ c₅ ^ 2 = (r₂ + r₅) ^ 2 ∧ dist c₃ c₄ ^ 2 = (r₃ + r₄) ^ 2 ∧
    dist c₃ c₅ ^ 2 = (r₃ + r₅) ^ 2 ∧ dist c₄ c₅ ^ 2 = (r₄ + r₅) ^ 2 ∧
    (1 / r₁ + 1 / r₂ + 1 / r₃ + 1 / r₄ + 1 / r₅) ^ 2 = 81 := by
  intro c₁ c₂ c₃ c₄ c₅ r₁ r₂ r₃ r₄ r₅
  have h3 : (1 / √3) ^ 2 = 1 / 3 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine ⟨by norm_num [r₁], by norm_num [r₂], by norm_num [r₃], by norm_num [r₄],
    by norm_num [r₅], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num [r₁, r₂, r₃, r₄, r₅]⟩ <;>
  · rw [dist_sq_fin3]; simp [c₁, c₂, c₃, c₄, c₅, r₁, r₂, r₃, r₄, r₅]; nlinarith [h3]

/-- **Witness for Ptolemy (concyclic).** `0, P = 8 + 4i, Q = 10, S = 8 - 4i` lie on the circle
`|z - 5| = 5`; the first disjunct holds: `√20·√80 + √20·√80 = 8·10`, both sides `80 ≠ 0`. -/
theorem l14w_ptolemy_concyclic :
    let K : ℂ := 5; let P : ℂ := ⟨8, 4⟩; let Q : ℂ := 10; let S : ℂ := ⟨8, -4⟩
    P ≠ 0 ∧ Q ≠ 0 ∧ S ≠ 0 ∧ ‖P - K‖ = ‖K‖ ∧ ‖Q - K‖ = ‖K‖ ∧ ‖S - K‖ = ‖K‖ ∧
    dist P Q * ‖S‖ + dist Q S * ‖P‖ = 80 ∧ dist P S * ‖Q‖ = 80 := by
  intro K P Q S
  have hK : ‖K‖ = 5 := l14h_norm (by norm_num) (by norm_num [K])
  have dPQ : dist P Q = √20 := l14h_dist (by positivity)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num [P, Q])
  have dQS : dist Q S = √20 := l14h_dist (by positivity)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num [Q, S])
  have nS : ‖S‖ = √80 := l14h_norm (by positivity) (by rw [Real.sq_sqrt (by norm_num)]; norm_num [S])
  have nP : ‖P‖ = √80 := l14h_norm (by positivity) (by rw [Real.sq_sqrt (by norm_num)]; norm_num [P])
  have key : √20 * √80 = 40 := by
    rw [← Real.sqrt_mul (by norm_num), show (20 : ℝ) * 80 = 40 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.re h; norm_num [P] at this
  · intro h; have := congrArg Complex.re h; norm_num [Q] at this
  · intro h; have := congrArg Complex.re h; norm_num [S] at this
  · rw [hK]; exact l14h_norm (by norm_num) (by norm_num [P, K])
  · rw [hK]; exact l14h_norm (by norm_num) (by norm_num [Q, K])
  · rw [hK]; exact l14h_norm (by norm_num) (by norm_num [S, K])
  · rw [dPQ, dQS, nS, nP, key]; norm_num
  · rw [l14h_dist (d := 8) (by norm_num) (by norm_num [P, S]),
      l14h_norm (d := 10) (by norm_num) (by norm_num [Q])]; norm_num

/-- **Witness for Ptolemy via inversion.** With `R² = 20`, the images of `P, Q, S` above are
`2 + i, 2, 2 - i` (three distinct points on the line `re = 2`), and the betweenness equality of
the conclusion holds: `1 + 1 = 2`. -/
theorem l14w_ptolemy_iff_dist_add_dist_invPt :
    inversion (0 : ℂ) (√20) ⟨8, 4⟩ = ⟨2, 1⟩ ∧ inversion (0 : ℂ) (√20) 10 = 2 ∧
    inversion (0 : ℂ) (√20) ⟨8, -4⟩ = ⟨2, -1⟩ ∧
    dist (⟨2, 1⟩ : ℂ) 2 + dist (2 : ℂ) ⟨2, -1⟩ = dist (⟨2, 1⟩ : ℂ) ⟨2, -1⟩ ∧
    dist (⟨2, 1⟩ : ℂ) 2 = 1 := by
  have h20 : √20 ^ 2 = 20 := Real.sq_sqrt (by norm_num)
  have inv : ∀ z : ℂ, inversion (0 : ℂ) (√20) z = ((20 / ‖z‖ ^ 2 : ℝ) : ℂ) * z := by
    intro z; simp [inversion, dist_zero_right, h20, div_pow, Complex.real_smul]
  have n1 : ‖(⟨8, 4⟩ : ℂ)‖ ^ 2 = 80 := by rw [l14h_norm (d := √80) (by positivity)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num), Real.sq_sqrt (by norm_num)]
  have n2 : ‖(10 : ℂ)‖ ^ 2 = 100 := by norm_num
  have n3 : ‖(⟨8, -4⟩ : ℂ)‖ ^ 2 = 80 := by rw [l14h_norm (d := √80) (by positivity)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num), Real.sq_sqrt (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [inv, n1]; apply Complex.ext <;> norm_num
  · rw [inv, n2]; apply Complex.ext <;> norm_num
  · rw [inv, n3]; apply Complex.ext <;> norm_num
  · rw [l14h_dist (d := 1) (by norm_num) (by norm_num), l14h_dist (d := 1) (by norm_num) (by norm_num),
      l14h_dist (d := 2) (by norm_num) (by norm_num)]; norm_num
  · exact l14h_dist (by norm_num) (by norm_num)

/-- **Witness for Ptolemy's inequality (strict case).** For the non-concyclic `P = 3`, `Q = 4i`,
`S = -3` (with `0`): `dist P S · ‖Q‖ = 24 < 30 = dist P Q · ‖S‖ + dist Q S · ‖P‖`. -/
theorem l14w_ptolemy_inequality :
    (3 : ℂ) ≠ 0 ∧ (⟨0, 4⟩ : ℂ) ≠ 0 ∧ (-3 : ℂ) ≠ 0 ∧
    dist (3 : ℂ) (-3) * ‖(⟨0, 4⟩ : ℂ)‖ = 24 ∧
    dist (3 : ℂ) ⟨0, 4⟩ * ‖(-3 : ℂ)‖ + dist (⟨0, 4⟩ : ℂ) (-3) * ‖(3 : ℂ)‖ = 30 := by
  refine ⟨by norm_num, ?_, by norm_num, ?_, ?_⟩
  · intro h; have := congrArg Complex.im h; norm_num at this
  · rw [l14h_dist (d := 6) (by norm_num) (by norm_num), l14h_norm (d := 4) (by norm_num) (by norm_num)]
    norm_num
  · rw [l14h_dist (d := 5) (by norm_num) (by norm_num), l14h_dist (d := 5) (by norm_num) (by norm_num)]
    norm_num

/-- **Witness for the classical Peaucellier cell** (`b² − a² = R²`). Connectors
`b = √26` to `A = 5 + i`, `B = 5 - i`; rhombus side `a = √10` with `P = 2`, `Q = 8`; `R = 4`.
All hypotheses hold and the conclusion is non-degenerate: `Q = 8 = 16/2` is the inverse of `P`,
`‖P‖·‖Q‖ = 16`, `P ≠ Q`. (Honest note: no witness with rational `a, b, R` was found by an
integer search up to 200; irrational link lengths are used.) -/
theorem l14w_peaucellier_classic :
    let A : ℂ := ⟨5, 1⟩; let B : ℂ := ⟨5, -1⟩; let P : ℂ := 2; let Q : ℂ := 8
    (4 : ℝ) ≠ 0 ∧ (√26) ^ 2 - (√10) ^ 2 = (4 : ℝ) ^ 2 ∧ ‖A‖ = √26 ∧ ‖B‖ = √26 ∧
    dist P A = √10 ∧ dist P B = √10 ∧ dist Q A = √10 ∧ dist Q B = √10 ∧ A ≠ B ∧ P ≠ Q ∧
    Q = inversion (0 : ℂ) 4 P ∧ ‖P‖ * ‖Q‖ = 16 := by
  intro A B P Q
  have s26 : √26 ^ 2 = 26 := Real.sq_sqrt (by norm_num)
  have s10 : √10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  refine ⟨by norm_num, by rw [s26, s10]; norm_num,
    l14h_norm (by positivity) (by rw [s26]; norm_num [A]),
    l14h_norm (by positivity) (by rw [s26]; norm_num [B]),
    l14h_dist (by positivity) (by rw [s10]; norm_num [P, A]),
    l14h_dist (by positivity) (by rw [s10]; norm_num [P, B]),
    l14h_dist (by positivity) (by rw [s10]; norm_num [Q, A]),
    l14h_dist (by positivity) (by rw [s10]; norm_num [Q, B]), ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.im h; norm_num [A, B] at this
  · intro h; have := congrArg Complex.re h; norm_num [P, Q] at this
  · simp [inversion, P, Q, dist_zero_right, Complex.real_smul]; norm_num
  · norm_num [P, Q]

/-- **Witness for the Peaucellier cell with the pivot inside** (`a² − b² = R²`). Connectors
`b = √2` to `A = 1 + i`, `B = 1 - i`; rhombus side `a = √10` with `P = 4`, `Q = -2`; `R = √8`.
The conclusion is non-degenerate: `Q = -2 = -(8/4)`, `‖P‖·‖Q‖ = 8`. -/
theorem l14w_peaucellier :
    let A : ℂ := ⟨1, 1⟩; let B : ℂ := ⟨1, -1⟩; let P : ℂ := 4; let Q : ℂ := -2
    √8 ≠ 0 ∧ (√10) ^ 2 - (√2) ^ 2 = (√8) ^ 2 ∧ ‖A‖ = √2 ∧ ‖B‖ = √2 ∧
    dist P A = √10 ∧ dist P B = √10 ∧ dist Q A = √10 ∧ dist Q B = √10 ∧ A ≠ B ∧ P ≠ Q ∧
    Q = -inversion (0 : ℂ) (√8) P ∧ ‖P‖ * ‖Q‖ = 8 := by
  intro A B P Q
  have s2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s8 : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have s10 : √10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  refine ⟨by positivity, by rw [s2, s8, s10]; norm_num,
    l14h_norm (by positivity) (by rw [s2]; norm_num [A]),
    l14h_norm (by positivity) (by rw [s2]; norm_num [B]),
    l14h_dist (by positivity) (by rw [s10]; norm_num [P, A]),
    l14h_dist (by positivity) (by rw [s10]; norm_num [P, B]),
    l14h_dist (by positivity) (by rw [s10]; norm_num [Q, A]),
    l14h_dist (by positivity) (by rw [s10]; norm_num [Q, B]), ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.im h; norm_num [A, B] at this
  · intro h; have := congrArg Complex.re h; norm_num [P, Q] at this
  · simp [inversion, P, Q, dist_zero_right, Complex.real_smul, div_pow]
    norm_num
  · norm_num [P, Q]

/-- **Witness for Descartes solve / Vieta.** For `k₁ = 2, k₂ = 2, k₃ = 3` the two solutions are
`k⁺ = 15`, `k⁻ = -1` (distinct); `k⁺ + k⁻ = 14 = 2·7` and `k⁺ k⁻ = -15`. -/
theorem l14w_descartes_vieta :
    ((2 : ℝ) + 2 + 3 + 15) ^ 2 - 2 * (2 ^ 2 + 2 ^ 2 + 3 ^ 2 + 15 ^ 2) = 0 ∧
    ((2 : ℝ) + 2 + 3 + -1) ^ 2 - 2 * (2 ^ 2 + 2 ^ 2 + 3 ^ 2 + (-1) ^ 2) = 0 ∧ (15 : ℝ) ≠ -1 ∧
    (15 : ℝ) = 2 + 2 + 3 + 2 * √(2 * 2 + 2 * 3 + 3 * 2) ∧
    (-1 : ℝ) = 2 + 2 + 3 - 2 * √(2 * 2 + 2 * 3 + 3 * 2) := by
  have h : √(2 * 2 + 2 * 3 + 3 * 2 : ℝ) = 4 := by
    rw [show (2 * 2 + 2 * 3 + 3 * 2 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> rw [h] <;> norm_num

/-- **Witness for integral Apollonian gaskets.** `(-1, 2, 2, 3)` is an integral solution; its
reflection in the first curvature is `(15, 2, 2, 3)`. -/
theorem l14w_apollonian_integral :
    ((-1 : ℤ) + 2 + 2 + 3) ^ 2 - 2 * ((-1) ^ 2 + 2 ^ 2 + 2 ^ 2 + 3 ^ 2) = 0 ∧
    (2 : ℤ) * (2 + 2 + 3) - (-1) = 15 := by norm_num

end Witnesses

end Inversion

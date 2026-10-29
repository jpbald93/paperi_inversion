import Inversion.Basic

/-!
# Ptolemy's theorem via inversion

Inverting in a circle centred at one of four points `0, P, Q, S` turns Ptolemy's identity
`|PQ|·|0S| + |QS|·|0P| = |PS|·|0Q|` into the boundary case `|P'Q'| + |Q'S'| = |P'S'|` of the
triangle inequality for the images, and the triangle inequality itself into Ptolemy's
inequality. If `0, P, Q, S` are concyclic, the images lie on a line, so one of the three
boundary equalities, i.e. one of the three Ptolemy identities, holds.
-/

namespace Inversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem dist_invPt_eq (R : ℝ) {P Q S : V} (hP : P ≠ 0) (hQ : Q ≠ 0) (hS : S ≠ 0) :
    dist (invPt R P) (invPt R Q) = R ^ 2 / (‖P‖ * ‖Q‖ * ‖S‖) * (dist P Q * ‖S‖) := by
  have hp : 0 < ‖P‖ := norm_pos_iff.2 hP
  have hq : 0 < ‖Q‖ := norm_pos_iff.2 hQ
  have hs : 0 < ‖S‖ := norm_pos_iff.2 hS
  rw [dist_invPt R hP hQ]
  field_simp

/-- **Algebraic reduction of Ptolemy's identity.** The Ptolemy identity for `0, P, Q, S` is
equivalent to the boundary case of the triangle inequality for the inverted points. -/
theorem ptolemy_iff_dist_add_dist_invPt {R : ℝ} (hR : R ≠ 0) {P Q S : V} (hP : P ≠ 0)
    (hQ : Q ≠ 0) (hS : S ≠ 0) :
    dist (invPt R P) (invPt R Q) + dist (invPt R Q) (invPt R S) = dist (invPt R P) (invPt R S) ↔
      dist P Q * ‖S‖ + dist Q S * ‖P‖ = dist P S * ‖Q‖ := by
  have hp : 0 < ‖P‖ := norm_pos_iff.2 hP
  have hq : 0 < ‖Q‖ := norm_pos_iff.2 hQ
  have hs : 0 < ‖S‖ := norm_pos_iff.2 hS
  have hc : R ^ 2 / (‖P‖ * ‖Q‖ * ‖S‖) ≠ 0 := by positivity
  rw [dist_invPt_eq R hP hQ hS, dist_invPt_eq R hQ hS hP, dist_invPt_eq R hP hS hQ,
    show ‖Q‖ * ‖S‖ * ‖P‖ = ‖P‖ * ‖Q‖ * ‖S‖ by ring, show ‖P‖ * ‖S‖ * ‖Q‖ = ‖P‖ * ‖Q‖ * ‖S‖ by ring,
    ← mul_add, mul_right_inj' hc]

/-- **Ptolemy's inequality**, from the triangle inequality for the inverted points. -/
theorem ptolemy_inequality {P Q S : V} (hP : P ≠ 0) (hQ : Q ≠ 0) (hS : S ≠ 0) :
    dist P S * ‖Q‖ ≤ dist P Q * ‖S‖ + dist Q S * ‖P‖ := by
  have hp : 0 < ‖P‖ := norm_pos_iff.2 hP
  have hq : 0 < ‖Q‖ := norm_pos_iff.2 hQ
  have hs : 0 < ‖S‖ := norm_pos_iff.2 hS
  have h := dist_triangle (invPt 1 P) (invPt 1 Q) (invPt 1 S)
  rw [dist_invPt_eq 1 hP hQ hS, dist_invPt_eq 1 hQ hS hP, dist_invPt_eq 1 hP hS hQ,
    show ‖Q‖ * ‖S‖ * ‖P‖ = ‖P‖ * ‖Q‖ * ‖S‖ by ring, show ‖P‖ * ‖S‖ * ‖Q‖ = ‖P‖ * ‖Q‖ * ‖S‖ by ring,
    ← mul_add] at h
  exact le_of_mul_le_mul_left h (by positivity)

/-- Equality in the triangle inequality holds exactly when the middle point lies between the
other two. -/
theorem dist_add_dist_eq_iff_wbtw (X Y Z : V) :
    dist X Y + dist Y Z = dist X Z ↔ Wbtw ℝ X Y Z :=
  dist_add_dist_eq_iff

/-- **Triangle-inequality boundary.** Three points are collinear iff one of the three triangle
inequalities between them is an equality. -/
theorem collinear_iff_dist_boundary (X Y Z : V) :
    Collinear ℝ ({X, Y, Z} : Set V) ↔
      dist X Y + dist Y Z = dist X Z ∨ dist Y Z + dist Z X = dist Y X ∨
        dist Z X + dist X Y = dist Z Y := by
  constructor
  · intro h
    rcases h.wbtw_or_wbtw_or_wbtw with h | h | h
    · exact Or.inl (dist_add_dist_eq_iff.2 h)
    · exact Or.inr (Or.inl (dist_add_dist_eq_iff.2 h))
    · exact Or.inr (Or.inr (dist_add_dist_eq_iff.2 h))
  · rintro (h | h | h)
    · exact (dist_add_dist_eq_iff.1 h).collinear
    · have e : ({Y, Z, X} : Set V) = {X, Y, Z} := by
        ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      exact e ▸ (dist_add_dist_eq_iff.1 h).collinear
    · have e : ({Z, X, Y} : Set V) = {X, Y, Z} := by
        ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      exact e ▸ (dist_add_dist_eq_iff.1 h).collinear

theorem inner_eq_re_im (z w : ℂ) : inner ℝ z w = z.re * w.re + z.im * w.im := by
  simp [Complex.inner]; ring

/-- Two points of the plane with the same inner product against `K ≠ 0` differ by a multiple
of `I * K`. -/
theorem exists_eq_smul_add {K Y Z : ℂ} (hK : K ≠ 0) (h : inner ℝ Y K = inner ℝ Z K) :
    ∃ r : ℝ, Y = r • (Complex.I * K) + Z := by
  rw [inner_eq_re_im, inner_eq_re_im] at h
  have hn : K.re ^ 2 + K.im ^ 2 ≠ 0 := by
    intro h0
    apply hK
    apply Complex.ext <;> simp <;> nlinarith [sq_nonneg K.re, sq_nonneg K.im]
  refine ⟨((Y.im - Z.im) * K.re - (Y.re - Z.re) * K.im) / (K.re ^ 2 + K.im ^ 2), ?_⟩
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, smul_eq_mul] <;> field_simp
  · linear_combination K.re * h
  · linear_combination K.im * h

/-- The images of points of a circle through the centre of inversion are collinear. -/
theorem collinear_invPt_of_concyclic {R : ℝ} {K P Q S : ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hS : S ≠ 0) (hPK : ‖P - K‖ = ‖K‖) (hQK : ‖Q - K‖ = ‖K‖) (hSK : ‖S - K‖ = ‖K‖) :
    Collinear ℝ ({invPt R P, invPt R Q, invPt R S} : Set ℂ) := by
  have hK : K ≠ 0 := by
    rintro rfl
    simp at hPK
    exact hP hPK
  rw [collinear_iff_of_mem (p₀ := invPt R P) (by simp)]
  refine ⟨Complex.I * K, ?_⟩
  have hp := inner_invPt_of_mem_circle R hP hPK
  intro Y hY
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
  rcases hY with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact exists_eq_smul_add hK (by rw [hp, inner_invPt_of_mem_circle R hQ hQK])
  · exact exists_eq_smul_add hK (by rw [hp, inner_invPt_of_mem_circle R hS hSK])

/-- **Ptolemy's theorem.** If `0, P, Q, S` lie on a circle, then one of the three Ptolemy
identities holds (the one in which the "middle" point appears on the right). -/
theorem ptolemy_concyclic {K P Q S : ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) (hS : S ≠ 0)
    (hPK : ‖P - K‖ = ‖K‖) (hQK : ‖Q - K‖ = ‖K‖) (hSK : ‖S - K‖ = ‖K‖) :
    dist P Q * ‖S‖ + dist Q S * ‖P‖ = dist P S * ‖Q‖ ∨
      dist Q S * ‖P‖ + dist S P * ‖Q‖ = dist Q P * ‖S‖ ∨
        dist S P * ‖Q‖ + dist P Q * ‖S‖ = dist S Q * ‖P‖ := by
  have h1 : (1 : ℝ) ≠ 0 := one_ne_zero
  rcases (collinear_iff_dist_boundary _ _ _).1
    (collinear_invPt_of_concyclic (R := 1) hP hQ hS hPK hQK hSK) with h | h | h
  · exact Or.inl ((ptolemy_iff_dist_add_dist_invPt h1 hP hQ hS).1 h)
  · exact Or.inr (Or.inl ((ptolemy_iff_dist_add_dist_invPt h1 hQ hS hP).1 h))
  · exact Or.inr (Or.inr ((ptolemy_iff_dist_add_dist_invPt h1 hS hP hQ).1 h))

end Inversion

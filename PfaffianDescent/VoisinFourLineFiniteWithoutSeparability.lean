import PfaffianDescent.VoisinFiniteProjectiveCone
import PfaffianDescent.TripleCompleteIntersectionHilbert
import AllCharacteristics.CubicLineAlgebra
import PfaffianDescent.VoisinFourLineRegularWithoutRadical

/-!
# Four noncontained cubic line sections give a finite intersection

The roots on a line may repeat. Their finite support still covers all
projective zeros, which is enough for finiteness of the triple intersection.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial Polynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubic_reducible_two_quadric_intersection_finite_of_four_nonzero_line_sections
    {L : Type u} [Field L] [IsAlgClosed L]
    (p q r : MvPolynomial (Fin 4) L)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (c : Cubic L 4) (hc : c.toMvPolynomial = p)
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hqfactor : q = l 0 * l 1)
    (hrfactor : r = m 0 * m 1)
    (u v : Fin 2 → Fin 2 → Vec L 4)
    (hu : ∀ a b, c.eval (u a b) ≠ 0)
    (hparam : ∀ a b (y : Fin 4 → L),
      (l a).eval y = 0 → (m b).eval y = 0 →
      ∃ s t : L, y = s • u a b + t • v a b) :
    IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  classical
  let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let T (a b : Fin 2) :=
    {z : L // z ∈ (AllCharacteristics.cubicLinePolynomial c (u a b) (v a b)).roots.toFinset}
  letI (a b : Fin 2) : Finite (T a b) := inferInstance
  let β := Σ a : Fin 2, Σ b : Fin 2, T a b
  letI : Finite β := inferInstance
  let x : β → Fin 4 → L := fun z => z.2.2.1 • u z.1 z.2.1 + v z.1 z.2.1
  have hcover : ∀ y ∈ MvPolynomial.zeroLocus L J.toIdeal,
      y = 0 ∨ ∃ (z : β) (t : L), y = t • x z := by
    intro y hy
    have hp0 : p.eval y = 0 := hy p (Ideal.subset_span (by simp))
    have hq0 : (l 0).eval y * (l 1).eval y = 0 := by
      have h := hy q (Ideal.subset_span (by simp))
      simpa [hqfactor, MvPolynomial.eval_mul] using h
    have hr0 : (m 0).eval y * (m 1).eval y = 0 := by
      have h := hy r (Ideal.subset_span (by simp))
      simpa [hrfactor, MvPolynomial.eval_mul] using h
    obtain ⟨a, ha⟩ : ∃ a : Fin 2, (l a).eval y = 0 := by
      rcases mul_eq_zero.mp hq0 with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨b, hb⟩ : ∃ b : Fin 2, (m b).eval y = 0 := by
      rcases mul_eq_zero.mp hr0 with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨s, t, hyrep⟩ := hparam a b y ha hb
    have hzero : c.eval (s • u a b + t • v a b) = 0 := by
      rw [hyrep] at hp0
      rw [← hc] at hp0
      change MvPolynomial.eval₂ (RingHom.id L)
        (s • u a b + t • v a b) c.toMvPolynomial = 0 at hp0
      rw [Cubic.eval_toMvPolynomial] at hp0
      exact hp0
    rcases (AllCharacteristics.finite_cubic_line_points_cover
      c (u a b) (v a b) (hu a b)).2 s t hzero with hz | ⟨z, w, hzw⟩
    · exact Or.inl (hyrep.trans hz)
    · exact Or.inr ⟨⟨a, b, z⟩, w, by simpa [x] using hyrep.trans hzw⟩
  exact isFinite_projective_of_finite_cone_coverage J x hcover

/-- Four genuine line sections whose cubic restrictions are nonzero make the
third quadric regular over the ground field. Repeated intersection roots are
allowed, so no separability or radicality is assumed. -/
theorem cubic_two_quadric_regular_descends_from_four_nonzero_line_sections
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (c : Cubic L 4) (hc : c.toMvPolynomial = p.map (algebraMap K L))
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hl : ∀ i, (l i).IsHomogeneous 1)
    (hm : ∀ i, (m i).IsHomogeneous 1)
    (hqfactor : q.map (algebraMap K L) = l 0 * l 1)
    (hrfactor : r.map (algebraMap K L) = m 0 * m 1)
    (u v : Fin 2 → Fin 2 → Vec L 4)
    (hu : ∀ a b, c.eval (u a b) ≠ 0)
    (huv : ∀ a b (t : L), t • u a b + v a b ≠ 0)
    (hlroots : ∀ a b, (l a).eval (u a b) = 0 ∧
      (l a).eval (v a b) = 0)
    (hmroots : ∀ a b, (m b).eval (u a b) = 0 ∧
      (m b).eval (v a b) = 0)
    (hparam : ∀ a b (y : Fin 4 → L),
      (l a).eval y = 0 → (m b).eval y = 0 →
      ∃ s t : L, y = s • u a b + t • v a b) :
    ∀ F : MvPolynomial (Fin 4) K,
      r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  let φ := algebraMap K L
  let pL := p.map φ
  let qL := q.map φ
  let rL := r.map φ
  let J := tripleCompleteIntersectionHomogeneousIdeal
    pL qL rL (hp.map φ) (hq.map φ) (hr.map φ)
  have hfinite : IsFinite (toBase J) :=
    cubic_reducible_two_quadric_intersection_finite_of_four_nonzero_line_sections
      pL qL rL (hp.map φ) (hq.map φ) (hr.map φ)
      c hc l m hqfactor hrfactor u v hu hparam
  obtain ⟨t, ht⟩ :=
    AllCharacteristics.cubicLinePolynomial_exists_root c (u 0 0) (v 0 0) (hu 0 0)
  let y := t • u 0 0 + v 0 0
  have hpzero : pL.eval y = 0 := by
    have h := AllCharacteristics.cubicLinePolynomial_eval₂
      (RingHom.id L) c (u 0 0) (v 0 0) t
    have hc0 : c.eval y = 0 := by
      change (AllCharacteristics.cubicLinePolynomial c (u 0 0) (v 0 0)).eval₂
        (RingHom.id L) t = c.eval y at h
      exact h.symm.trans (by simpa using ht)
    change (p.map (algebraMap K L)).eval y = 0
    rw [← hc]
    change MvPolynomial.eval₂ (RingHom.id L) y c.toMvPolynomial = 0
    rw [Cubic.eval_toMvPolynomial]
    exact hc0
  have hlzero : (l 0).eval y = 0 := by
    change (l 0).eval₂ (RingHom.id L) y = 0
    simpa [y, (hlroots 0 0).1, (hlroots 0 0).2] using
      (eval₂_homogeneous_degree_one_line (RingHom.id L)
        (l 0) (hl 0) (u 0 0) (v 0 0) t)
  have hmzero : (m 0).eval y = 0 := by
    change (m 0).eval₂ (RingHom.id L) y = 0
    simpa [y, (hmroots 0 0).1, (hmroots 0 0).2] using
      (eval₂_homogeneous_degree_one_line (RingHom.id L)
        (m 0) (hm 0) (u 0 0) (v 0 0) t)
  have hqzero : qL.eval y = 0 := by
    change (q.map (algebraMap K L)).eval y = 0
    rw [hqfactor, MvPolynomial.eval_mul]
    simp [hlzero]
  have hrzero : rL.eval y = 0 := by
    change (r.map (algebraMap K L)).eval y = 0
    rw [hrfactor, MvPolynomial.eval_mul]
    simp [hmzero]
  have hI : ∀ a ∈ J.toIdeal, a.eval y = 0 := by
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      tripleCompleteIntersectionIdeal]
    intro a ha
    have hker : Ideal.span ({pL, qL, rL} : Set (MvPolynomial (Fin 4) L)) ≤
        RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id L) y) := by
      apply Ideal.span_le.mpr
      intro z hz
      rcases hz with rfl | rfl | rfl
      · exact hpzero
      · exact hqzero
      · exact hrzero
    exact hker ha
  have hnonempty : Nonempty (scheme J) := by
    obtain ⟨z, -⟩ := point_of_coordinates J (RingHom.id L) y
      (huv 0 0 t) (fun a ha ↦ hI a ha)
    exact ⟨z (IsLocalRing.closedPoint L)⟩
  exact cubic_two_quadric_regular_descends_of_finite_nonempty_extension
    p q r hp hq hr hfinite hnonempty

end PfaffianDescent

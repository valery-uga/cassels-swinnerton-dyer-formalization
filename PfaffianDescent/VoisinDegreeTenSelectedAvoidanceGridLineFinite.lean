import PfaffianDescent.VoisinFourLineFiniteWithoutSeparability

/-! # A nine-line cubic grid gives a proper cubic intersection

The finite-cone argument for four lines applies equally to products of three
planes. This records actual finiteness and descent of the third regular
equation for the resulting cubic--cubic--cubic intersection.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Polynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Nine noncontained line sections make the literal intersection of the
cubic with two products of three planes finite. Repeated roots are permitted
for this finiteness statement. -/
theorem voisinDegreeTenSelectedAvoidance_nineLine_intersection_finite
    {L : Type u} [Field L] [IsAlgClosed L]
    (p q r : MvPolynomial (Fin 4) L)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (c : Cubic L 4) (hc : c.toMvPolynomial = p)
    (l m : Fin 3 → MvPolynomial (Fin 4) L)
    (hqfactor : q = ∏ i, l i) (hrfactor : r = ∏ i, m i)
    (u v : Fin 3 → Fin 3 → Vec L 4)
    (hu : ∀ a b, c.eval (u a b) ≠ 0)
    (hparam : ∀ a b (y : Fin 4 → L),
      (l a).eval y = 0 → (m b).eval y = 0 →
      ∃ s t : L, y = s • u a b + t • v a b) :
    IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  classical
  let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let T (a b : Fin 3) :=
    {z : L // z ∈ (cubicLinePolynomial c (u a b) (v a b)).roots.toFinset}
  letI (a b : Fin 3) : Finite (T a b) := inferInstance
  let β := Σ a : Fin 3, Σ b : Fin 3, T a b
  letI : Finite β := inferInstance
  let x : β → Fin 4 → L := fun z => z.2.2.1 • u z.1 z.2.1 + v z.1 z.2.1
  have hcover : ∀ y ∈ MvPolynomial.zeroLocus L J.toIdeal,
      y = 0 ∨ ∃ (z : β) (t : L), y = t • x z := by
    intro y hy
    have hp0 : p.eval y = 0 := hy p (Ideal.subset_span (by simp))
    have hq0 : ∏ a, (l a).eval y = 0 := by
      have h := hy q (Ideal.subset_span (by simp))
      simpa [hqfactor, map_prod] using h
    have hr0 : ∏ b, (m b).eval y = 0 := by
      have h := hy r (Ideal.subset_span (by simp))
      simpa [hrfactor, map_prod] using h
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.mp hq0
    obtain ⟨b, -, hb⟩ := Finset.prod_eq_zero_iff.mp hr0
    obtain ⟨s, t, hyrep⟩ := hparam a b y ha hb
    have hzero : c.eval (s • u a b + t • v a b) = 0 := by
      rw [hyrep] at hp0
      rw [← hc] at hp0
      change MvPolynomial.eval₂ (RingHom.id L)
        (s • u a b + t • v a b) c.toMvPolynomial = 0 at hp0
      rw [Cubic.eval_toMvPolynomial] at hp0
      exact hp0
    rcases (finite_cubic_line_points_cover c (u a b) (v a b) (hu a b)).2
        s t hzero with hz | ⟨z, w, hzw⟩
    · exact Or.inl (hyrep.trans hz)
    · exact Or.inr ⟨⟨a, b, z⟩, w, by simpa [x] using hyrep.trans hzw⟩
  exact isFinite_projective_of_finite_cone_coverage J x hcover

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness and a nonzero geometric point of the actual cubic triple
intersection imply native regularity over the original coefficient field. -/
theorem voisinDegreeTenSelectedAvoidance_cubic_regular_descends_of_finite_nonempty
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hfinite : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L))
      (hp.map (algebraMap K L)) (hq.map (algebraMap K L))
      (hr.map (algebraMap K L)))))
    (hnonempty : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L))
      (hp.map (algebraMap K L)) (hq.map (algebraMap K L))
      (hr.map (algebraMap K L))))) :
    ∀ F : MvPolynomial (Fin 4) K,
      r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  let φ := algebraMap K L
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map φ) (q.map φ) (r.map φ)
      (hp.map φ) (hq.map φ) (hr.map φ))) := hfinite
  intro F hF
  have hFL : (r.map φ) * F.map φ ∈
      Ideal.span ({p.map φ, q.map φ} : Set (MvPolynomial (Fin 4) L)) := by
    have hm := Ideal.mem_map_of_mem (MvPolynomial.map φ) hF
    simpa [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using hm
  have hmemL := third_regular_of_finite_degrees
    (p.map φ) (q.map φ) (r.map φ)
    (hp.map φ) (hq.map φ) (hr.map φ) (by decide) (by decide)
    hnonempty (F.map φ) hFL
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  have hmap : I.map (MvPolynomial.map φ) =
      Ideal.span ({p.map φ, q.map φ} : Set (MvPolynomial (Fin 4) L)) := by
    simp [I, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change F ∈ I
  rw [← mvPolynomial_comap_map_coefficientExtension (K := L) I,
    Ideal.mem_comap, hmap]
  exact hmemL

set_option backward.isDefEq.respectTransparency false in
/-- A concrete grid of nine genuine line sections gives an actual third
regular cubic over the ground field. -/
theorem voisinDegreeTenSelectedAvoidance_regular_of_nineLine_grid
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (c : Cubic L 4) (hc : c.toMvPolynomial = p.map (algebraMap K L))
    (l m : Fin 3 → MvPolynomial (Fin 4) L)
    (hl : ∀ i, (l i).IsHomogeneous 1) (hm : ∀ i, (m i).IsHomogeneous 1)
    (hqfactor : q.map (algebraMap K L) = ∏ i, l i)
    (hrfactor : r.map (algebraMap K L) = ∏ i, m i)
    (u v : Fin 3 → Fin 3 → Vec L 4)
    (hu : ∀ a b, c.eval (u a b) ≠ 0)
    (huv : ∀ a b (t : L), t • u a b + v a b ≠ 0)
    (hlroots : ∀ a b, (l a).eval (u a b) = 0 ∧ (l a).eval (v a b) = 0)
    (hmroots : ∀ a b, (m b).eval (u a b) = 0 ∧ (m b).eval (v a b) = 0)
    (hparam : ∀ a b (y : Fin 4 → L),
      (l a).eval y = 0 → (m b).eval y = 0 →
      ∃ s t : L, y = s • u a b + t • v a b) :
    ∀ F : MvPolynomial (Fin 4) K,
      r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  classical
  let φ := algebraMap K L
  let pL := p.map φ
  let qL := q.map φ
  let rL := r.map φ
  let J := tripleCompleteIntersectionHomogeneousIdeal
    pL qL rL (hp.map φ) (hq.map φ) (hr.map φ)
  have hfinite : IsFinite (toBase J) :=
    voisinDegreeTenSelectedAvoidance_nineLine_intersection_finite
      pL qL rL (hp.map φ) (hq.map φ) (hr.map φ)
      c hc l m hqfactor hrfactor u v hu hparam
  obtain ⟨t, ht⟩ := cubicLinePolynomial_exists_root c (u 0 0) (v 0 0) (hu 0 0)
  let y := t • u 0 0 + v 0 0
  have hpzero : pL.eval y = 0 := by
    have h := cubicLinePolynomial_eval₂ (RingHom.id L) c (u 0 0) (v 0 0) t
    have hc0 : c.eval y = 0 := by
      change (cubicLinePolynomial c (u 0 0) (v 0 0)).eval₂ (RingHom.id L) t = c.eval y at h
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
    rw [hqfactor, map_prod]
    exact Finset.prod_eq_zero_iff.mpr ⟨0, Finset.mem_univ _, hlzero⟩
  have hrzero : rL.eval y = 0 := by
    change (r.map (algebraMap K L)).eval y = 0
    rw [hrfactor, map_prod]
    exact Finset.prod_eq_zero_iff.mpr ⟨0, Finset.mem_univ _, hmzero⟩
  have hI : ∀ a ∈ J.toIdeal, a.eval y = 0 := by
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal, tripleCompleteIntersectionIdeal]
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
  exact voisinDegreeTenSelectedAvoidance_cubic_regular_descends_of_finite_nonempty
    p q r hp hq hr hfinite hnonempty

end PfaffianDescent

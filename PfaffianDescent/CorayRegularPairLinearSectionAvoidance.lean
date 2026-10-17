import PfaffianDescent.TwoQuadricsNoIrrelevantSocle
import PfaffianDescent.ProjectiveIdealSaturation
import PfaffianDescent.ProjectiveFiniteFamilyHyperplane
import PfaffianDescent.CorayProjectiveIntersectionChartDimension

/-! A genuine linear-equation selector for the literal p/q quotient.
The installed two_quadrics_no_irrelevant_annihilator is degree-independent.
Its socle vanishing makes every associated-prime bad subspace proper;
projective points supply further proper bad subspaces. One finite-union
avoidance constructs BOTH the third-equation nonzerodivisor and avoidance
of the actual specified finite family. No cone primeness is assumed.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A regular original pair admits an actual degree-one polynomial which
is a nonzerodivisor modulo the literal (p,q), and simultaneously avoids an
arbitrary finite family of its OWN actual projective points. -/
theorem regular_pair_exists_linear_nonzerodivisor_avoiding_finite_projective_family
    (p q : MvPolynomial (Fin 4) K) {a b : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    {ι : Type*} [Finite ι]
    (point : ι → scheme (projectiveIntersectionIdeal p q hp hq)) :
    ∃ H : MvPolynomial (Fin 4) K, H.IsHomogeneous 1 ∧
      (∀ x : MvPolynomial (Fin 4) K,
        H * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
      (∀ j, Ideal.Quotient.mk (projectiveIntersectionIdeal p q hp hq).toIdeal H ∉
        (point j).asHomogeneousIdeal) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let A := CoordinateRing I
  let W := grading I 1
  have hsocle : ∀ x : CoordinateRing I,
      (∀ j : Fin 4, coordinate I j * x = 0) → x = 0 := by
    change ∀ x : MvPolynomial (Fin 4) K ⧸ I.toIdeal,
      (∀ j : Fin 4, Ideal.Quotient.mk I.toIdeal (MvPolynomial.X j) * x = 0) → x = 0
    dsimp only [I]
    rw [projectiveIntersectionIdeal_toIdeal]
    exact fun x hx => two_quadrics_no_irrelevant_annihilator p q hp0 hrel x hx
  have hcoordinate := coordinate_avoidance_of_no_irrelevant_annihilator I hsocle
  let Associated := {P : Ideal A // P ∈ associatedPrimes A A}
  letI : Finite Associated := associatedPrimes.finite A A
  let badIdeal : Associated ⊕ ι → Ideal A := fun j => match j with
    | Sum.inl P => P.1
    | Sum.inr k => (point k).asHomogeneousIdeal.toIdeal
  let bad (j : Associated ⊕ ι) : Submodule K W :=
    ((badIdeal j).restrictScalars K).comap W.subtype
  have hbad (j : Associated ⊕ ι) : bad j ≠ ⊤ := by
    intro htop
    cases j with
    | inl P =>
      obtain ⟨k, hk⟩ := hcoordinate P.1 P.2
      have hmem : (⟨coordinate I k, coordinate_mem I k⟩ : W) ∈ bad (Sum.inl P) := by
        rw [htop]
        exact Submodule.mem_top
      exact hk hmem
    | inr k =>
      apply (point k).not_irrelevant_le
      change (HomogeneousIdeal.irrelevant (grading I)).toIdeal ≤
        (point k).asHomogeneousIdeal.toIdeal
      rw [irrelevant_eq_coordinateIdeal]
      apply Ideal.span_le.mpr
      rintro _ ⟨r, rfl⟩
      have hmem : (⟨coordinate I r, coordinate_mem I r⟩ : W) ∈ bad (Sum.inr k) := by
        rw [htop]
        exact Submodule.mem_top
      exact hmem
  obtain ⟨y, hy⟩ := exists_vector_avoiding_finite_submodules bad hbad
  have hyregular : (y : A) ∈ nonZeroDivisors A := by
    have hnot : (y : A) ∉ ⋃ P ∈ associatedPrimes A A, (P : Set A) := by
      intro hmem
      obtain ⟨P, hP, hyP⟩ := Set.mem_iUnion₂.mp hmem
      exact hy (Sum.inl ⟨P, hP⟩) hyP
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors A] at hnot
    change (y : A) ∈ (nonZeroDivisors A : Set A)
    simpa only [Set.mem_compl_iff, not_not] using hnot
  have hymem : (y : A) ∈
      (homogeneousSubmodule (Fin 4) K 1).map
        (Ideal.Quotient.mkₐ K I.toIdeal).toLinearMap := y.2
  obtain ⟨H, hH, hHy⟩ := Submodule.mem_map.mp hymem
  have hHy' : Ideal.Quotient.mk I.toIdeal H = (y : A) := hHy
  refine ⟨H, hH, ?_, ?_⟩
  · intro x hx
    have hx' : H * x ∈ I.toIdeal := by
      simpa only [I, projectiveIntersectionIdeal_toIdeal] using hx
    have hzero : Ideal.Quotient.mk I.toIdeal H * Ideal.Quotient.mk I.toIdeal x = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hx'
    have hHregular : Ideal.Quotient.mk I.toIdeal H ∈ nonZeroDivisors A :=
      hHy'.symm ▸ hyregular
    have hxzero := (mul_left_mem_nonZeroDivisors_eq_zero_iff hHregular).mp hzero
    have hxin := Ideal.Quotient.eq_zero_iff_mem.mp hxzero
    simpa only [I, projectiveIntersectionIdeal_toIdeal] using hxin
  · intro j
    rw [hHy']
    exact hy (Sum.inr j)

end PfaffianDescent.Coray

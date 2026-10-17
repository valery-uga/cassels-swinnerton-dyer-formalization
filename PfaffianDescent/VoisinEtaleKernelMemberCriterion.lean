import PfaffianDescent.VoisinDegreeEightEtaleMemberCriterion
import PfaffianDescent.VoisinEightFiniteAlgebraQuadraticKernel
import PfaffianDescent.VoisinGenericSplitEtale

/-!
# An étale member anywhere in the full quadratic kernel

The generic split witness is an explicit quadratic combination, whereas the
universal singular-member family uses an arbitrary basis of the same kernel.
These lemmas move between a nonzero basis coordinate and the corresponding
rescaled étale complete intersection.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Multiplying the third equation of a homogeneous complete intersection
by a nonzero field scalar does not change its projective scheme. -/
theorem tripleCompleteIntersectionHomogeneousIdeal_smul_third
    {K : Type u} [Field K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (a : K) (ha : a ≠ 0) :
    tripleCompleteIntersectionHomogeneousIdeal p q (a • r)
      hp hq (by simpa only [MvPolynomial.smul_eq_C_mul] using hr.C_mul a) =
    tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr := by
  apply HomogeneousIdeal.ext
  simp only [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionIdeal]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | hs
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
    · rw [hs]
      have hmem : r ∈ Ideal.span ({p, q, r} : Set _) :=
        Ideal.subset_span (by simp)
      rw [MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ (C a) hmem
  · apply Ideal.span_le.mpr
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | hs
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
    · rw [hs]
      have hmem : a • r ∈ Ideal.span ({p, q, a • r} : Set _) :=
        Ideal.subset_span (by simp)
      have hmul := Ideal.mul_mem_left
        (Ideal.span ({p, q, a • r} : Set _)) (C a⁻¹) hmem
      simpa [MvPolynomial.smul_eq_C_mul, ← mul_assoc, ha] using hmul

/-- Étaleness is unchanged by a nonzero scalar multiple of the third
defining equation. -/
theorem tripleCompleteIntersection_etale_smul_third
    {K : Type u} [Field K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (a : K) (ha : a ≠ 0)
    (hEtale : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      p q (a • r) hp hq
        (by simpa only [MvPolynomial.smul_eq_C_mul] using hr.C_mul a))) := by
  rw [tripleCompleteIntersectionHomogeneousIdeal_smul_third
    p q r hp hq hr a ha]
  exact hEtale

/-- Any nonzero étale member of the full quadratic restriction kernel makes
the canonical singular-member locus proper; the member need not be a chosen
basis vector. -/
theorem cubicTwoQuadricRestrictionKernelSingularParameterLocus_ne_univ_of_etale_kernel_member
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2) (x : Fin 4 → A)
    (hrvan : r.eval₂ (algebraMap K A) x = 0) (hrne : r ≠ 0)
    (hEtale : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    cubicTwoQuadricRestrictionKernelSingularParameterLocus p q hp hq x ≠
      Set.univ := by
  classical
  let W := LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)
  let b := quadraticRestrictionKernelBasis (K := K) x
  let v := quadraticRestrictionKernelFrame (K := K) x
  let rW : W := ⟨⟨r, hr⟩, by
    apply LinearMap.mem_ker.mpr
    simpa only [homogeneousSectionRestriction_apply] using hrvan⟩
  let c := b.repr rW
  have hcne : c ≠ 0 := by
    intro hc0
    have hrW0 : rW = 0 := b.repr.injective (by simpa [c] using hc0)
    exact hrne (congrArg (fun z : W => z.1.1) hrW0)
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    apply hcne
    ext i
    by_contra hci
    exact h ⟨i, hci⟩
  let d : Fin (finrank K W) → K := fun j => (c i)⁻¹ * c j
  have hdi : d i = 1 := by
    simp [d, inv_mul_cancel₀ hi]
  have hrepr : r = ∑ j, C (c j) * (v j).1 := by
    have hsum := b.sum_repr rW
    have hval := congrArg (fun z : W => z.1.1) hsum
    simpa only [c, v, quadraticRestrictionKernelFrame,
      Submodule.coe_sum, Submodule.coe_smul,
      MvPolynomial.smul_eq_C_mul] using hval.symm
  let r' : MvPolynomial (Fin 4) K := (c i)⁻¹ • r
  have hr' : r'.IsHomogeneous 2 := by
    simpa only [r', MvPolynomial.smul_eq_C_mul] using hr.C_mul (c i)⁻¹
  have hrepr' : r' = ∑ j, C (d j) * (v j).1 := by
    calc
      r' = C ((c i)⁻¹) * r := by simp [r', MvPolynomial.smul_eq_C_mul]
      _ = C ((c i)⁻¹) * ∑ j, C (c j) * (v j).1 := by rw [hrepr]
      _ = ∑ j, C (d j) * (v j).1 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [d, map_mul, mul_assoc]
  have hEtale' : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r' hp hq hr')) := by
    exact tripleCompleteIntersection_etale_smul_third
      p q r hp hq hr (c i)⁻¹ (inv_ne_zero hi) hEtale
  exact cubicTwoQuadricUniversalSingularParameterLocus_ne_univ_of_etale_member
    p q r' hp hq hr' v d i hdi hrepr' hEtale'

/-- The actual generic eight-point datum satisfies the proper-member input
for Voisin's degree-eight residual construction. Its fixed first quadric is
the first split quadric; the second split quadric gives an étale witness in
the entire intrinsic restriction kernel. -/
theorem exists_generic_eight_finite_datum_with_proper_quadratic_member_and_minor
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ (y : Fin 8 → Fin 4 → L)
        (hzero : ∀ i, p.eval (y i) = 0)
        (c₀ : Fin 4 → L)
        (hc₀ : ∀ i, (homogeneousLinearForm c₀).eval (y i) ≠ 0)
        (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
        (A : Spec (.of L) ⟶
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
        (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
        (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8),
        (∀ i, (A ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left =
            projectiveVectorSchemePointInLinearChart
              (equationIdeal p hp) c₀ (y i)
              (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc₀ i)) ∧
        A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B ∧
        (∃ hB : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _,
          D = projectiveConfigurationFiniteSubschemeAt
            (grading (equationIdeal p hp))
            (hypersurfaceToBase p hp) 8 B hB) ∧
        Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
        DegreeEightQuadraticRestrictionKernelProperMemberExists p hp D ∧
        Function.Surjective
          (homogeneousSectionRestriction (K := L)
            (fun j i => y i j) 2) ∧
        (∀ i, (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y i) = 0 ∧
          (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y i) = 0) ∧
        IsUnit (eightPointQuadraticEvaluationMinor m y).det := by
  dsimp only
  letI : Infinite L := CharZero.infinite L
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  let q : MvPolynomial (Fin 4) L := X 1 * X 2
  let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let hq : q.IsHomogeneous 2 := (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
  let hr : r.IsHomogeneous 2 := (isHomogeneous_X L 3).mul
    (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
      (isHomogeneous_X L 3))
  obtain ⟨hsmooth, y, hzero, c₀, hc₀, m, A, B, D,
    hcoord, hAB, hD, hEt, hdatum, hsurj₀, hquadrics, hm⟩ :=
    exists_generic_eight_finite_datum_with_exact_quadratic_kernel_and_minor K φ
  let f := D.val.subschemeι ≫ hypersurfaceToBase p hp
  letI : IsFinite f := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  letI : FiniteDimensional L Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite f
  obtain ⟨c, x, hlinear, hcubic, hgen, hsurj, hker,
    he, hzOne, hmap⟩ := hdatum
  let z : CoordinateRing (equationIdeal p hp) :=
    Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading (equationIdeal p hp) 1 :=
    polynomial_class_mem_grading (equationIdeal p hp)
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
    ![⟨q, hq⟩, ⟨r, hr⟩]
  have hker' : LinearMap.ker
      (homogeneousSectionRestriction (K := L) x 2) =
      Submodule.span L (Set.range Q) := hker
  have hqmem : (⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2) ∈
      LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) := by
    rw [hker']
    apply Submodule.subset_span
    exact ⟨0, rfl⟩
  have hrmem : (⟨r, hr⟩ : homogeneousSubmodule (Fin 4) L 2) ∈
      LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) := by
    rw [hker']
    apply Submodule.subset_span
    exact ⟨1, rfl⟩
  have hqvan : q.eval₂ (algebraMap L Γ(D.val.subscheme, ⊤)) x = 0 :=
    LinearMap.mem_ker.mp hqmem
  have hrvan : r.eval₂ (algebraMap L Γ(D.val.subscheme, ⊤)) x = 0 :=
    LinearMap.mem_ker.mp hrmem
  have hq0 : q ≠ 0 := by
    intro hzero
    exact (standard_split_quadric_pair_linearIndependent (L := L)).ne_zero 0
      (by simpa [q] using hzero)
  have hr0 : r ≠ 0 := by
    intro hzero
    exact (standard_split_quadric_pair_linearIndependent (L := L)).ne_zero 1
      (by simpa [r] using hzero)
  have hproper :=
    cubicTwoQuadricRestrictionKernelSingularParameterLocus_ne_univ_of_etale_kernel_member
      p q r hp hq hr x hrvan hr0 (generic_split_intersection_etale K φ)
  have hmember :
      DegreeEightQuadraticRestrictionKernelProperMemberExists p hp D :=
    ⟨z, hz, x, he, hzOne, hgen, hmap,
      q, hq, hqvan, hq0, hproper⟩
  exact ⟨hsmooth, y, hzero, c₀, hc₀, m, A, B, D,
    hcoord, hAB, hD, hEt, hmember, hsurj₀, hquadrics, hm⟩

/-- The original proper-member endpoint, recovered from the witness that
also retains the selected unit quadratic evaluation minor. -/
theorem exists_generic_eight_finite_datum_with_proper_quadratic_member
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
        (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8),
        (∃ hB : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _,
          D = projectiveConfigurationFiniteSubschemeAt
            (grading (equationIdeal p hp))
            (hypersurfaceToBase p hp) 8 B hB) ∧
        Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
        DegreeEightQuadraticRestrictionKernelProperMemberExists p hp D := by
  dsimp only
  obtain ⟨hsmooth, _, _, _, _, _, _, B, D, _, _, hD, hEt, hmember, _, _, _⟩ :=
    exists_generic_eight_finite_datum_with_proper_quadratic_member_and_minor K φ
  exact ⟨hsmooth, B, D, hD, hEt, hmember⟩

/-- The finite étale degree-four residual of a fixed degree-eight datum. -/
def FiniteEightDatumHasDisjointEtaleDegreeFourResidual
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
    EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
    Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
    Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R))

/-- The generic smooth cubic has the actual disjoint finite étale
degree-four residual of the explicit eight-point configuration. -/
theorem exists_generic_eight_and_disjoint_etale_degree_four_residual
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
        (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8),
        (∃ hB : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _,
          D₈ = projectiveConfigurationFiniteSubschemeAt
            (grading (equationIdeal p hp))
            (hypersurfaceToBase p hp) 8 B hB) ∧
        Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
        FiniteEightDatumHasDisjointEtaleDegreeFourResidual p hp D₈ := by
  dsimp only
  letI : Infinite L := CharZero.infinite L
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hsmooth, B, D₈, hB, hD, hmember⟩ :=
    exists_generic_eight_finite_datum_with_proper_quadratic_member K φ
  letI : Smooth (hypersurfaceToBase p hp) := hsmooth
  have hp0 : p ≠ 0 := by
    intro hzero
    have hpoint := genericCubicTensor_baseChange_standard_point_ne_zero K φ
    simp [p, hzero] at hpoint
  obtain ⟨R, hdegree, hR, hdisjoint⟩ :=
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_restrictionKernelProperMember
      p hp hp0 D₈ hmember
  exact ⟨hsmooth, B, D₈, hB, hD, R, hdegree, hR, hdisjoint⟩

end PfaffianDescent

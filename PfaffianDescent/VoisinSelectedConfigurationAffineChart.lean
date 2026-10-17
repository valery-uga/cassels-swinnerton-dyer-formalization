import PfaffianDescent.VoisinEtaleKernelMemberCriterion
import AllCharacteristics.ProjectiveConfigurationAffineCharts
import AllCharacteristics.VoisinGenericCubicPoint
import PfaffianDescent.VoisinGenericCubicResidual
import PfaffianDescent.VoisinGenericFourLineSeparability
import AllCharacteristics.OrderedCommonOpenCoordinateLifts
import AllCharacteristics.ConfigurationFreeQuotientCharts

/-!
# Affine ordered and unordered charts through a selected configuration

The free finite-quotient construction gives simultaneous affine charts for
an ordered configuration and its unordered image.  This file records the
pointwise form needed to spread the selected quadratic witness.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The generic cubic remains a nonzero polynomial after the coefficient
field is embedded in an algebraically closed extension. -/
theorem genericCubicTensor_toMvPolynomial_ne_zero_after_baseChange
    (K : Type u) [Field K]
    {L : Type u} [Field L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    ((genericCubicTensor K).map φ).toMvPolynomial ≠ 0 := by
  intro hzero
  have hbase := genericCubicTensor_base_eval_ne_zero_baseChange K φ
  have heval := Cubic.eval_toMvPolynomial (RingHom.id L)
    ((genericCubicTensor K).map φ)
    (fun k => φ (genericFourLineBase K k))
  rw [hzero] at heval
  simp at heval
  exact hbase heval.symm

/-- A configuration represented by eight vectors in one linear chart lies
in the corresponding common affine open of the ordered family. -/
theorem ordered_eight_configuration_mem_common_linear_basicOpen
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (y : Fin 8 → Fin 4 → L)
    (hzero : ∀ i, p.eval (y i) = 0)
    (c : Fin 4 → L)
    (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
    (hcoord : ∀ k, (A ≫ Over.Hom.left
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left =
        projectiveVectorSchemePointInLinearChart
          (equationIdeal p hp) c (y k)
          (cubicVector_zero_equationIdeal p hp (y k) (hzero k)) (hc k)) :
    let z : CoordinateRing (equationIdeal p hp) :=
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c)
    (A (IsLocalRing.closedPoint L)).val ∈
      orderedFamilyCommonOpen (hypersurfaceToBase p hp)
        (Proj.basicOpen (grading (equationIdeal p hp)) z) 8 := by
  dsimp only
  apply (mem_orderedFamilyCommonOpen_iff
    (hypersurfaceToBase p hp)
    (Proj.basicOpen (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
        (homogeneousLinearForm c))) 8
    (A (IsLocalRing.closedPoint L)).val).mpr
  intro k
  have hk := congrArg
    (fun f : Spec (.of L) ⟶ scheme (equationIdeal p hp) =>
      f (IsLocalRing.closedPoint L)) (hcoord k)
  have hpoint :
      Over.Hom.left (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k)
          ((A (IsLocalRing.closedPoint L)).val) =
        projectiveVectorSchemePointInLinearChart
          (equationIdeal p hp) c (y k)
          (cubicVector_zero_equationIdeal p hp (y k) (hzero k)) (hc k)
            (IsLocalRing.closedPoint L) := by
    change ((A ≫ Over.Hom.left
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left)
        (IsLocalRing.closedPoint L) = _
    exact hk
  have hmem := projectiveVectorSchemePointInLinearChart_mem_basicOpen
    (equationIdeal p hp) c (y k)
    (cubicVector_zero_equationIdeal p hp (y k) (hzero k)) (hc k)
  exact hpoint.symm ▸ hmem

/-- An ordered field-valued point and its unordered quotient image lie in
compatible affine open charts whose quotient square commutes. -/
theorem exists_cubicConfiguration_compatible_affineCharts_at_fieldPoint
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
    (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
    (hAB : A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B) :
    ∃ (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
      (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
      (j : Q ⟶ cubicConfigurationBase p hp 8)
      (r : U ⟶ Q),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧
      A (IsLocalRing.closedPoint L) ∈ Set.range i ∧
      B (IsLocalRing.closedPoint L) ∈ Set.range j ∧
      i ≫ configurationQuotientMap (equationIdeal p hp) 8 = r ≫ j := by
  let x := A (IsLocalRing.closedPoint L)
  obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hi, hτi, b, hb, j, hj,
    hxi, hcomm, _⟩ :=
    exists_projectiveConfigurationQuotient_affineChart
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8 x
  let Q := affineSchemeActionQuotient (Equiv.Perm (Fin 8))
    τ hτ₁ hτcomp b hb
  let r : U ⟶ Q := affineSchemeActionQuotientMap
    (Equiv.Perm (Fin 8)) τ hτ₁ hτcomp b hb
  have hQa : IsAffine Q := inferInstance
  obtain ⟨u, hu⟩ := hxi
  have hBj : B (IsLocalRing.closedPoint L) ∈ Set.range j := by
    refine ⟨r u, ?_⟩
    have hABpoint := congrArg
      (fun f : Spec (.of L) ⟶ cubicConfigurationBase p hp 8 =>
        f (IsLocalRing.closedPoint L)) hAB
    have hcommpoint := congrArg
      (fun f : U ⟶ cubicConfigurationBase p hp 8 => f u) hcomm
    have hquotx :
        configurationQuotientMap (equationIdeal p hp) 8 (i u) =
          configurationQuotientMap (equationIdeal p hp) 8 x :=
      congrArg _ hu
    exact hcommpoint.symm.trans (hquotx.trans hABpoint)
  exact ⟨U, Q, hUa, hQa, i, j, r, hi, hj, ⟨u, hu⟩, hBj, hcomm⟩

/-- The quotient charts may be chosen inside a prescribed common affine
open containing all eight projective coordinates of the ordered point. -/
theorem exists_cubicConfiguration_compatible_affineCharts_inside_commonOpen
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (V : (hypersurface p hp).affineOpens)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
    (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
    (hAB : A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B)
    (hAV : (A (IsLocalRing.closedPoint L)).val ∈
      orderedFamilyCommonOpen (hypersurfaceToBase p hp) V.val 8) :
    ∃ (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
      (i : U ⟶ (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left)
      (j : Q ⟶ cubicConfigurationBase p hp 8)
      (r : U ⟶ Q),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ Surjective r ∧
      IsIntegralHom r ∧ IsFinite r ∧
      A (IsLocalRing.closedPoint L) ∈ Set.range i ∧
      B (IsLocalRing.closedPoint L) ∈ Set.range j ∧
      i ≫ configurationQuotientMap (equationIdeal p hp) 8 = r ≫ j ∧
      (∀ z : U, (i z).val ∈
        orderedFamilyCommonOpen (hypersurfaceToBase p hp) V.val 8) := by
  let x := A (IsLocalRing.closedPoint L)
  obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hi, hτi, b, hb, j, hj,
    hxi, hcomm, _, hinside⟩ :=
    exists_projectiveConfigurationQuotient_affineChart_inside_commonOpen
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8 V x hAV
  let Q := affineSchemeActionQuotient (Equiv.Perm (Fin 8))
    τ hτ₁ hτcomp b hb
  let r : U ⟶ Q := affineSchemeActionQuotientMap
    (Equiv.Perm (Fin 8)) τ hτ₁ hτcomp b hb
  have hQa : IsAffine Q := inferInstance
  obtain ⟨u, hu⟩ := hxi
  have hBj : B (IsLocalRing.closedPoint L) ∈ Set.range j := by
    refine ⟨r u, ?_⟩
    have hABpoint := congrArg
      (fun f : Spec (.of L) ⟶ cubicConfigurationBase p hp 8 =>
        f (IsLocalRing.closedPoint L)) hAB
    have hcommpoint := congrArg
      (fun f : U ⟶ cubicConfigurationBase p hp 8 => f u) hcomm
    have hquotx :
        configurationQuotientMap (equationIdeal p hp) 8 (i u) =
          configurationQuotientMap (equationIdeal p hp) 8 x :=
      congrArg _ hu
    exact hcommpoint.symm.trans (hquotx.trans hABpoint)
  have hsurjr : Surjective r := by
    dsimp [r]
    infer_instance
  have hintr : IsIntegralHom r := by
    dsimp [r]
    infer_instance
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  have hret : Etale r := by
    dsimp [r]
    exact etale_affineConfigurationActionQuotientMap
      (hypersurfaceToBase p hp) 8 τ hτ₁ hτcomp b hb i hτi
  letI : Etale r := hret
  have hfinr : IsFinite r := by
    exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType r).mpr
      ⟨hintr, inferInstance⟩
  exact ⟨U, Q, hUa, hQa, i, j, r, hi, hj, hsurjr, hintr, hfinr, ⟨u, hu⟩,
    hBj, hcomm, hinside⟩

/-- On an integral configuration base, the same unordered affine chart
through the selected point also contains the canonical generic point. -/
theorem exists_cubicConfiguration_compatible_affineCharts_at_genericPoint
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
    (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
    (hAB : A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B) :
    ∃ (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
      (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
      (j : Q ⟶ cubicConfigurationBase p hp 8)
      (r : U ⟶ Q),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧
      A (IsLocalRing.closedPoint L) ∈ Set.range i ∧
      B (IsLocalRing.closedPoint L) ∈ Set.range j ∧
      genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j ∧
      i ≫ configurationQuotientMap (equationIdeal p hp) 8 = r ≫ j := by
  obtain ⟨U, Q, hUa, hQa, i, j, r, hi, hj, hAi, hBj, hcomm⟩ :=
    exists_cubicConfiguration_compatible_affineCharts_at_fieldPoint
      p hp A B hAB
  letI : IsOpenImmersion j := hj
  have hgeneric : genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j :=
    (genericPoint_specializes (B (IsLocalRing.closedPoint L))).mem_open
      (IsOpenImmersion.isOpen_range j) hBj
  exact ⟨U, Q, hUa, hQa, i, j, r, hi, hj, hAi, hBj, hgeneric, hcomm⟩

/-- Smoothness and one finite étale length-eight datum provide the
integrality needed in the preceding generic-point chart theorem. -/
theorem exists_cubicConfiguration_compatible_affineCharts_of_smooth
    {L : Type u} [Field L] [CharZero L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)]
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
    (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
    (hAB : A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B) :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hp0 8 D
    ∃ (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
      (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
      (j : Q ⟶ cubicConfigurationBase p hp 8)
      (r : U ⟶ Q),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧
      A (IsLocalRing.closedPoint L) ∈ Set.range i ∧
      B (IsLocalRing.closedPoint L) ∈ Set.range j ∧
      genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j ∧
      i ≫ configurationQuotientMap (equationIdeal p hp) 8 = r ≫ j := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hp0 8 D
  exact exists_cubicConfiguration_compatible_affineCharts_at_genericPoint
    p hp A B hAB

/-- A selected eight-point presentation in one linear chart on an arbitrary
smooth cubic admits compatible integral ordered and unordered affine charts,
contains the selected field point, reaches the unordered generic point, and
carries regular lifts of all eight projective coordinates. -/
theorem exists_selectedEight_commonAffineCharts_of_smooth
    {L : Type u} [Field L] [CharZero L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)]
    (y : Fin 8 → Fin 4 → L) (hzero : ∀ k, p.eval (y k) = 0)
    (c : Fin 4 → L)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
    (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
    (hcoord : ∀ k, (A ≫ Over.Hom.left
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left =
        projectiveVectorSchemePointInLinearChart
          (equationIdeal p hp) c (y k)
          (cubicVector_zero_equationIdeal p hp (y k) (hzero k)) (hc k))
    (hAB : A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B) :
    ∃ (hInt : IsIntegral (cubicConfigurationBase p hp 8)),
      letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
      ∃ (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
        (i : U ⟶ (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).left)
        (j : Q ⟶ cubicConfigurationBase p hp 8)
        (r : U ⟶ Q),
        IsOpenImmersion i ∧ IsOpenImmersion j ∧ Surjective r ∧
        IsIntegralHom r ∧ IsFinite r ∧
        IsIntegral U ∧ IsIntegral Q ∧
        A (IsLocalRing.closedPoint L) ∈ Set.range i ∧
        B (IsLocalRing.closedPoint L) ∈ Set.range j ∧
        genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j ∧
        i ≫ configurationQuotientMap (equationIdeal p hp) 8 = r ≫ j ∧
        (∀ u : U, (i u).val ∈ orderedFamilyCommonOpen
          (hypersurfaceToBase p hp)
          (Proj.basicOpen (grading (equationIdeal p hp))
            (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
              (homogeneousLinearForm c))) 8) ∧
        (∃ aU : Spec (.of L) ⟶ U, aU ≫ i = A) ∧
        (∀ k : Fin 8,
          ∃ t : U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
              (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
                (homogeneousLinearForm c)))),
            t ≫ Proj.awayι (grading (equationIdeal p hp))
              (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
                (homogeneousLinearForm c))
              (polynomial_class_mem_grading (equationIdeal p hp)
                (homogeneousLinearForm c)
                (homogeneousLinearForm_isHomogeneous c))
              (by decide : 0 < 1) =
                (i ≫ Over.Hom.left (orderedFamilyConfigurationι
                  (hypersurfaceToBase p hp) 8)) ≫
                  (orderedFamilyCoordinate
                    (hypersurfaceToBase p hp) 8 k).left) := by
  let hInt : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hp0 8 D
  letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
  let z : CoordinateRing (equationIdeal p hp) :=
    Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading (equationIdeal p hp) 1 :=
    polynomial_class_mem_grading (equationIdeal p hp)
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  let V : (hypersurface p hp).affineOpens :=
    ⟨Proj.basicOpen (grading (equationIdeal p hp)) z,
      Proj.isAffineOpen_basicOpen (grading (equationIdeal p hp)) z hz
        (by decide : 0 < 1)⟩
  have hAV : (A (IsLocalRing.closedPoint L)).val ∈
      orderedFamilyCommonOpen (hypersurfaceToBase p hp) V.val 8 :=
    ordered_eight_configuration_mem_common_linear_basicOpen
      p hp y hzero c hc A hcoord
  obtain ⟨U, Q, hUa, hQa, i, j, r, hi, hj, hsurjr, hintr, hfinr,
    hAi, hBj, hcomm, hinside⟩ :=
    exists_cubicConfiguration_compatible_affineCharts_inside_commonOpen
      p hp V A B hAB hAV
  letI : IsOpenImmersion j := hj
  have hgeneric : genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j :=
    (genericPoint_specializes (B (IsLocalRing.closedPoint L))).mem_open
      (IsOpenImmersion.isOpen_range j) hBj
  letI : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 8).left
    exact isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
      p hp hp0 8 D
  letI : IsOpenImmersion i := hi
  letI : Nonempty U := ⟨Classical.choose hAi⟩
  letI : Nonempty Q := ⟨Classical.choose hBj⟩
  have hUi : IsIntegral U := isIntegral_of_isOpenImmersion i
  have hQi : IsIntegral Q := isIntegral_of_isOpenImmersion j
  let jlin := Proj.awayι (grading (equationIdeal p hp)) z hz
    (by decide : 0 < 1)
  haveI : IsOpenImmersion jlin := by
    dsimp only [jlin]
    infer_instance
  have hcommon : ∀ u : U, (i u).val ∈
      orderedFamilyCommonOpen (hypersurfaceToBase p hp)
        jlin.opensRange 8 := by
    intro u
    rw [Proj.opensRange_awayι]
    exact hinside u
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  have hlifts := @exists_orderedConfiguration_coordinate_lifts
    _ _ U _ (hypersurfaceToBase p hp)
    (isSeparated_homogeneousToBase (equationIdeal p hp))
    jlin (show IsOpenImmersion jlin from inferInstance) i hcommon
  obtain ⟨aU, haU⟩ := exists_fieldPoint_lift_through_openImmersion
    i A hAi
  exact ⟨hInt, U, Q, hUa, hQa, i, j, r, hi, hj, hsurjr, hintr, hfinr,
    hUi, hQi, hAi, hBj, hgeneric, hcomm, hinside, ⟨aU, haU⟩, hlifts⟩

/-- The selected proper-member witness and the canonical generic
configuration point lie in one actual affine open of the unordered
configuration space. -/
theorem exists_generic_eight_properMember_affineChart_reaching_generic
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ (y : Fin 8 → Fin 4 → L)
        (hzero : ∀ i, p.eval (y i) = 0)
        (c : Fin 4 → L)
        (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
        (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
        (A : Spec (.of L) ⟶
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
        (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
        (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8),
        IsUnit (eightPointQuadraticEvaluationMinor m y).det ∧
        (∀ k, (A ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left =
            projectiveVectorSchemePointInLinearChart
              (equationIdeal p hp) c (y k)
              (cubicVector_zero_equationIdeal p hp (y k) (hzero k)) (hc k)) ∧
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
        ∃ (hInt : IsIntegral (cubicConfigurationBase p hp 8)),
          letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
          ∃ (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
            (i : U ⟶ (orderedFamilyConfigurationOver
              (hypersurfaceToBase p hp) 8).left)
            (j : Q ⟶ cubicConfigurationBase p hp 8)
            (r : U ⟶ Q),
            IsOpenImmersion i ∧ IsOpenImmersion j ∧ Surjective r ∧
            IsIntegralHom r ∧ IsFinite r ∧
            IsIntegral U ∧ IsIntegral Q ∧
            A (IsLocalRing.closedPoint L) ∈ Set.range i ∧
            B (IsLocalRing.closedPoint L) ∈ Set.range j ∧
            genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j ∧
            i ≫ configurationQuotientMap (equationIdeal p hp) 8 = r ≫ j ∧
            (∀ u : U, (i u).val ∈ orderedFamilyCommonOpen
              (hypersurfaceToBase p hp)
              (Proj.basicOpen (grading (equationIdeal p hp))
                (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
                  (homogeneousLinearForm c))) 8) ∧
            (∃ aU : Spec (.of L) ⟶ U, aU ≫ i = A) ∧
            (∀ k : Fin 8,
              ∃ t : U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
                (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
                  (homogeneousLinearForm c)))),
                t ≫ Proj.awayι (grading (equationIdeal p hp))
                  (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
                    (homogeneousLinearForm c))
                  (polynomial_class_mem_grading (equationIdeal p hp)
                    (homogeneousLinearForm c)
                    (homogeneousLinearForm_isHomogeneous c))
                  (by decide : 0 < 1) =
                  (i ≫ Over.Hom.left (orderedFamilyConfigurationι
                    (hypersurfaceToBase p hp) 8)) ≫
                    (orderedFamilyCoordinate
                      (hypersurfaceToBase p hp) 8 k).left) := by
  dsimp only
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hsmooth, y, hzero, c, hc, m, A, B, D,
    hcoord, hAB, hD, hEt, hmember, hsurj, hquadrics, hm⟩ :=
    exists_generic_eight_finite_datum_with_proper_quadratic_member_and_minor K φ
  letI : Smooth (hypersurfaceToBase p hp) := hsmooth
  letI : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) := hEt
  have hp0 : p ≠ 0 :=
    genericCubicTensor_toMvPolynomial_ne_zero_after_baseChange K φ
  let hInt : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hp0 8 D
  letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
  let z : CoordinateRing (equationIdeal p hp) :=
    Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading (equationIdeal p hp) 1 :=
    polynomial_class_mem_grading (equationIdeal p hp)
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  let V : (hypersurface p hp).affineOpens :=
    ⟨Proj.basicOpen (grading (equationIdeal p hp)) z,
      Proj.isAffineOpen_basicOpen (grading (equationIdeal p hp)) z hz
        (by decide : 0 < 1)⟩
  have hAV : (A (IsLocalRing.closedPoint L)).val ∈
      orderedFamilyCommonOpen (hypersurfaceToBase p hp) V.val 8 :=
    ordered_eight_configuration_mem_common_linear_basicOpen
      p hp y hzero c hc A hcoord
  obtain ⟨U, Q, hUa, hQa, i, j, r, hi, hj, hsurjr, hintr, hfinr,
    hAi, hBj, hcomm, hinside⟩ :=
    exists_cubicConfiguration_compatible_affineCharts_inside_commonOpen
      p hp V A B hAB hAV
  letI : IsOpenImmersion j := hj
  have hgeneric : genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j :=
    (genericPoint_specializes (B (IsLocalRing.closedPoint L))).mem_open
      (IsOpenImmersion.isOpen_range j) hBj
  letI : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 8).left
    exact isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
      p hp hp0 8 D
  letI : IsOpenImmersion i := hi
  letI : Nonempty U := ⟨Classical.choose hAi⟩
  letI : Nonempty Q := ⟨Classical.choose hBj⟩
  have hUi : IsIntegral U := isIntegral_of_isOpenImmersion i
  have hQi : IsIntegral Q := isIntegral_of_isOpenImmersion j
  let jlin := Proj.awayι (grading (equationIdeal p hp)) z hz
    (by decide : 0 < 1)
  haveI : IsOpenImmersion jlin := by
    dsimp [jlin]
    infer_instance
  have hcommon : ∀ u : U, (i u).val ∈
      orderedFamilyCommonOpen (hypersurfaceToBase p hp) jlin.opensRange 8 := by
    intro u
    rw [Proj.opensRange_awayι]
    exact hinside u
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  have hlifts := @exists_orderedConfiguration_coordinate_lifts
    _ _ U _ (hypersurfaceToBase p hp)
    (isSeparated_homogeneousToBase (equationIdeal p hp))
    jlin (show IsOpenImmersion jlin from inferInstance) i hcommon
  obtain ⟨aU, haU⟩ := exists_fieldPoint_lift_through_openImmersion
    i A hAi
  exact ⟨hsmooth, y, hzero, c, hc, m, A, B, D,
    hm, hcoord, hAB, hD, hEt, hmember, hsurj, hquadrics, hInt,
    U, Q, hUa, hQa, i, j, r, hi, hj, hsurjr, hintr, hfinr,
    hUi, hQi, hAi, hBj, hgeneric,
    hcomm, hinside, ⟨aU, haU⟩, hlifts⟩

end PfaffianDescent

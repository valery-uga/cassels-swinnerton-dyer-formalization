import PfaffianDescent.VoisinSmoothSelectedActualEightPresentation
import PfaffianDescent.VoisinSelectedConfigurationAffineChart
import PfaffianDescent.VoisinResidueCommonLinearChart
import PfaffianDescent.VoisinSmoothCompatibleAffineCharts

/-! The selected generic cubic supplies all common-chart data needed
for the actual eight-point comparison. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

structure SmoothCompatibleEightCharts
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) where
  hpne : p ≠ 0
  smooth : Smooth (hypersurfaceToBase p hp)
  D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8
  etale : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  baseIntegral : IsIntegral (cubicConfigurationBase p hp 8)
  U : Scheme.{u}
  Q : Scheme.{u}
  integralU : IsIntegral U
  integralQ : IsIntegral Q
  i : U ⟶ (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  j : Q ⟶ cubicConfigurationBase p hp 8
  r : U ⟶ Q
  openI : IsOpenImmersion i
  openJ : IsOpenImmersion j
  surjectiveR : Surjective r
  hcomm : i ≫ configurationQuotientMap (equationIdeal p hp) 8 = r ≫ j
  ell : MvPolynomial (Fin 4) K
  hell : ell.IsHomogeneous 1
  lifts : ∀ k : Fin 8,
    ∃ t : U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell))),
      t ≫ Proj.awayι (grading (equationIdeal p hp))
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
        (polynomial_class_mem_grading (equationIdeal p hp) ell hell)
        (by decide : 0 < 1) =
        (i ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left

/-- Every nonzero smooth cubic over a characteristic-zero field, together
with a finite étale degree-eight datum, admits the compatible common affine
chart package used by the selected generic construction.  The chosen point
may have a nontrivial residue field; its descended coordinates supply a
ground-field linear chart. -/
theorem exists_smoothCompatibleEightCharts
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    Nonempty (SmoothCompatibleEightCharts p hp) := by
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  let hBase : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth p hp hpne
  letI : IsIntegral (cubicConfigurationBase p hp 8) := hBase
  let hOrdered : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left :=
    isIntegral_orderedCubicConfiguration_of_smooth p hp hpne
  letI : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left := hOrdered
  obtain ⟨z, hz⟩ :=
    exists_smoothCubic_orderedEight_detectingCoordinates p hp hpne
  obtain ⟨c, hzc⟩ :=
    detectingCoordinates_mem_orderedFamilyCommonLinearBasicOpen
      p hp z hz
  let ell : MvPolynomial (Fin 4) K := homogeneousLinearForm c
  let zc : CoordinateRing (equationIdeal p hp) :=
    Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell
  have hzcdeg : zc ∈ grading (equationIdeal p hp) 1 :=
    polynomial_class_mem_grading (equationIdeal p hp) ell
      (homogeneousLinearForm_isHomogeneous c)
  let V : (hypersurface p hp).affineOpens :=
    ⟨Proj.basicOpen (grading (equationIdeal p hp)) zc,
      Proj.isAffineOpen_basicOpen (grading (equationIdeal p hp)) zc
        hzcdeg (by decide : 0 < 1)⟩
  have hzV : z.val ∈ orderedFamilyCommonOpen
      (hypersurfaceToBase p hp) V.val 8 := by
    simpa only [V, zc, ell] using hzc
  obtain ⟨U, Q, hUa, hQa, i, j, r, hi, hj, hsurjr, hintr, hfinr,
    hzi, hzj, hgeneric, hcomm, hinside⟩ :=
    exists_cubicConfiguration_compatible_affineCharts_inside_commonOpen_at_point
      p hp V z hzV
  letI : IsOpenImmersion i := hi
  letI : IsOpenImmersion j := hj
  letI : Nonempty U := ⟨Classical.choose hzi⟩
  letI : Nonempty Q := ⟨Classical.choose hzj⟩
  let hUi : IsIntegral U := isIntegral_of_isOpenImmersion i
  let hQi : IsIntegral Q := isIntegral_of_isOpenImmersion j
  let jlin := Proj.awayι (grading (equationIdeal p hp)) zc hzcdeg
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
  have hlifts := @exists_orderedConfiguration_coordinate_lifts
    _ _ U _ (hypersurfaceToBase p hp)
    (isSeparated_homogeneousToBase (equationIdeal p hp))
    jlin (show IsOpenImmersion jlin from inferInstance) i hcommon
  exact ⟨{
    hpne := hpne
    smooth := inferInstance
    D := D
    etale := inferInstance
    baseIntegral := hBase
    U := U
    Q := Q
    integralU := hUi
    integralQ := hQi
    i := i
    j := j
    r := r
    openI := hi
    openJ := hj
    surjectiveR := hsurjr
    hcomm := hcomm
    ell := ell
    hell := homogeneousLinearForm_isHomogeneous c
    lifts := hlifts }⟩

/-- The explicit selected eight-point construction supplies a smooth,
finite-étale compatible chart package. -/
theorem exists_genericCubic_smoothCompatibleEightCharts
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Nonempty (SmoothCompatibleEightCharts p hp) := by
  dsimp only
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hsmooth, y, hzero, c, hc, m, A, B, D,
    hm, hcoord, hAB, hD, hEt, hmember, hsurj, hquadrics,
    hInt, U, Q, hUa, hQa, i, j, r, hi, hj, hsurjr,
    hintr, hfinr, hUi, hQi, hAi, hBj, hgenericQ,
    hcomm, hinside, ⟨aU, haU⟩, ht⟩ :=
    exists_generic_eight_properMember_affineChart_reaching_generic K φ
  exact ⟨{
    hpne := genericCubicTensor_toMvPolynomial_ne_zero_after_baseChange K φ
    smooth := hsmooth
    D := D
    etale := hEt
    baseIntegral := hInt
    U := U
    Q := Q
    integralU := hUi
    integralQ := hQi
    i := i
    j := j
    r := r
    openI := hi
    openJ := hj
    surjectiveR := hsurjr
    hcomm := hcomm
    ell := homogeneousLinearForm c
    hell := homogeneousLinearForm_isHomogeneous c
    lifts := ht }⟩

end PfaffianDescent

import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationNativeCoefficientFinite
import PfaffianDescent.VoisinGenericCubicPoint

/-! # Actual generic-three evaluation of the original Serre extension -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual pullback of the original degree-eleven Serre extension has
a nonzero compatible section vanishing on the actual generic-three datum.
The function-field geometry and finite-datum field property are proved
from the original smooth cubic and original finite etale rank-three datum. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_generic_exists_nonzero_section
    (K : Type u) [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : Module.finrank K L = 11)
    (e : SerreExtensionSequenceData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hne :
      letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e
          (schemeModules_hasExt _)) (show 1 + 1 = 2 by omega) ≠ 0)
    (D₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    [Etale (D₀.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 3) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 3 D₀
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 3).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫
        cubicConfigurationToBase p hp 3),
    let P := p.map a.hom
    let hP := hp.map a.hom
    let X := hypersurface P hP
    let f := cubicClosedPointSerreDegreeThreeEvaluationCoefficientMap a.hom p hp
    let N : X.Modules := (Scheme.Modules.pullback f).obj (show (hypersurface p hp).Modules from e.E)
    let D := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
    ∃ s : N.sections, s ≠ SerreExtensionData.zeroSection N ∧
      BundleSectionZeroLocus.pullbackSection D.val.subschemeι N
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison D.val.subschemeι) s =
          SerreExtensionData.zeroSection ((Scheme.Modules.pullback D.val.subschemeι).obj N) := by
  letI : IsIntegral (cubicConfigurationBase p hp 3) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 3 D₀
  intro a ha
  let F := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  let P := p.map a.hom
  let hP := hp.map a.hom
  let X := hypersurface P hP
  let f := cubicClosedPointSerreDegreeThreeEvaluationCoefficientMap a.hom p hp
  let N : X.Modules := (Scheme.Modules.pullback f).obj (show (hypersurface p hp).Modules from e.E)
  let D := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  have hField : IsField Γ(D.val.subscheme, ⊤) :=
    cubicConfigurationGenericFiniteSubscheme_isField_of_smooth p hp hp0 3 D₀
      (0 : Fin 3) a ha
  obtain ⟨s, hs, hz⟩ := cubicClosedPointSerreDegreeThreeEvaluation_native_coefficient_finite_exists_nonzero
    K p hp hp0 i hi hL e hne F D hField
  refine ⟨N.unitHomEquiv s, ?_, ?_⟩
  · intro h
    apply hs
    have hh : s = N.unitHomEquiv.symm (SerreExtensionData.zeroSection N) := by
      simpa only [Equiv.symm_apply_apply] using congrArg N.unitHomEquiv.symm h
    exact hh.trans (SerreExtensionData.unitHomEquiv_symm_zeroSection N)
  · exact (cubicClosedPointSerreDegreeThreeEvaluationMap_eq_zero_iff_pullbackSection
      (hypersurfaceToBase P hP) D.val.subschemeι N s).mp hz

end PfaffianDescent.ProjectiveNegativeTwist

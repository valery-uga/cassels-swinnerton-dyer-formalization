import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationNative
import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationFiniteKernel

/-! # Actual evaluation on the original rank-three finite field datum -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual restriction target of the original native bundle has exactly
six dimensions on the actual rank-three finite field datum. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_native_finite_finrank_eq_six
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
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
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (hField : IsField Γ(D.val.subscheme, ⊤)) :
    Module.finrank K (SchemeModuleGlobalSectionsOver
      (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ((Scheme.Modules.pullback D.val.subschemeι).obj
        (show (hypersurface p hp).Modules from e.E))) = 6 := by
  let e' := cubicClosedPointSerreFreeNeighborhood_native_serreData K p hp hp0 i e hne
  let C := cubicClosedPointSerreFreeNeighborhood_native_rankTwoAffineCover K p hp hp0 i e hne
  exact cubicClosedPointSerreDegreeThreeEvaluationFiniteDimension_finrank_eq_six
    (hypersurfaceToBase p hp) e' C D hField

/-- The original native Serre bundle has a nonzero actual section vanishing
on the actual rank-three finite field datum itself. No target dimension,
fiber coordinate, section-comparison certificate, or source-dimension
certificate is an input. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_native_finite_exists_nonzero
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
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (hField : IsField Γ(D.val.subscheme, ⊤)) :
    ∃ s : SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
        (show (hypersurface p hp).Modules from e.E),
      s ≠ 0 ∧ cubicClosedPointSerreDegreeThreeEvaluationMap (hypersurfaceToBase p hp)
        D.val.subschemeι (show (hypersurface p hp).Modules from e.E) s = 0 := by
  letI : Infinite K := CharZero.infinite K
  letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
    schemeModules_hasExt _
  let e' := cubicClosedPointSerreFreeNeighborhood_native_serreData K p hp hp0 i e hne
  let C := cubicClosedPointSerreFreeNeighborhood_native_rankTwoAffineCover K p hp hp0 i e hne
  have hsections := cubicClosedPointSerreSection_finrank_ge_nine K p hp hp0 i hi hL e
  exact cubicClosedPointSerreDegreeThreeEvaluationFiniteKernel_exists_nonzero
    (hypersurfaceToBase p hp) e' C D hField hsections

/-- The same conclusion in the actual compatible-section model, with
literal pullback zero on the original finite datum. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_native_finite_exists_nonzero_section
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
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (hField : IsField Γ(D.val.subscheme, ⊤)) :
    ∃ s : e.E.sections, s ≠ SerreExtensionData.zeroSection e.E ∧
      BundleSectionZeroLocus.pullbackSection D.val.subschemeι
        (show (hypersurface p hp).Modules from e.E)
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison D.val.subschemeι) s =
          SerreExtensionData.zeroSection
            ((Scheme.Modules.pullback D.val.subschemeι).obj
              (show (hypersurface p hp).Modules from e.E)) := by
  obtain ⟨s, hs, hz⟩ := cubicClosedPointSerreDegreeThreeEvaluation_native_finite_exists_nonzero
    K p hp hp0 i hi hL e hne D hField
  refine ⟨e.E.unitHomEquiv s, ?_, ?_⟩
  · intro h
    apply hs
    have hh := congrArg e.E.unitHomEquiv.symm h
    simpa only [Equiv.symm_apply_apply, SerreExtensionData.unitHomEquiv_symm_zeroSection] using hh
  · exact (cubicClosedPointSerreDegreeThreeEvaluationMap_eq_zero_iff_pullbackSection
      (hypersurfaceToBase p hp) D.val.subschemeι (show (hypersurface p hp).Modules from e.E) s).mp hz

end PfaffianDescent.ProjectiveNegativeTwist

import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationCoefficient
import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationPullbackFiniteKernel

/-! # A section of the original Serre extension vanishing on a coefficient-extended datum -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal coefficient pullback of the original extension has a
nonzero actual global section vanishing on the actual rank-three finite
field datum. Its source dimensions, target dimensions, and geometric
comparison maps are constructed. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_native_coefficient_finite_exists_nonzero
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
    (F : Type u) [Field F] [Algebra K F]
    (D : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))) 3)
    (hField : IsField Γ(D.val.subscheme, ⊤)) :
    let f := cubicClosedPointSerreDegreeThreeEvaluationCoefficientMap (algebraMap K F) p hp
    let N := (Scheme.Modules.pullback f).obj (show (hypersurface p hp).Modules from e.E)
    ∃ s : SchemeModuleGlobalSectionsOver
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))) N,
      s ≠ 0 ∧ cubicClosedPointSerreDegreeThreeEvaluationMap
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        D.val.subschemeι N s = 0 := by
  letI : Infinite K := CharZero.infinite K
  letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
    schemeModules_hasExt _
  let e' := cubicClosedPointSerreFreeNeighborhood_native_serreData K p hp hp0 i e hne
  let C := cubicClosedPointSerreFreeNeighborhood_native_rankTwoAffineCover K p hp hp0 i e hne
  have hnine := cubicClosedPointSerreSection_finrank_ge_nine K p hp hp0 i hi hL e
  have hbc := cubicClosedPointSerreDegreeThreeEvaluationBaseChange_finrank_eq
    K p hp hp0 i hi hL e hne F
  have hcoeff := cubicClosedPointSerreDegreeThreeEvaluationCoefficient_finrank_eq_pullback
    (F := F) p hp (show (hypersurface p hp).Modules from e.E)
  have hsections : 9 ≤ Module.finrank F (SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicClosedPointSerreDegreeThreeEvaluationCoefficientMap (algebraMap K F) p hp)).obj
          (show (hypersurface p hp).Modules from e.E))) := by
    rw [← hcoeff, hbc]
    exact hnine
  exact cubicClosedPointSerreDegreeThreeEvaluationPullbackFiniteKernel_exists_nonzero
    e' C (cubicClosedPointSerreDegreeThreeEvaluationCoefficientMap (algebraMap K F) p hp)
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))) D hField hsections

end PfaffianDescent.ProjectiveNegativeTwist

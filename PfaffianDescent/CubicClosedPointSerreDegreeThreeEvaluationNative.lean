import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationKernel
import PfaffianDescent.CubicClosedPointSerreSectionDimension
import Mathlib.Algebra.CharZero.Infinite

/-! # Nonzero native Serre sections vanishing at a degree-three field point -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original degree-eleven Serre extension has a nonzero actual section
vanishing at an actual degree-three field point. Its nine source dimensions
and six target dimensions are proved from the actual geometry. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_native_exists_nonzero
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
    {A : Type u} [Field A] [Algebra K A]
    (j : Spec (.of A) ⟶ hypersurface p hp)
    (hj : j ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (hA : Module.finrank K A = 3) :
    ∃ s : SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
        (show (hypersurface p hp).Modules from e.E),
      s ≠ 0 ∧ cubicClosedPointSerreDegreeThreeEvaluationMap (hypersurfaceToBase p hp) j
        (show (hypersurface p hp).Modules from e.E) s = 0 := by
  letI : Infinite K := CharZero.infinite K
  letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
    schemeModules_hasExt _
  let e' := cubicClosedPointSerreFreeNeighborhood_native_serreData K p hp hp0 i e hne
  let C := cubicClosedPointSerreFreeNeighborhood_native_rankTwoAffineCover K p hp hp0 i e hne
  have hsections := cubicClosedPointSerreSection_finrank_ge_nine K p hp hp0 i hi hL e
  exact cubicClosedPointSerreDegreeThreeEvaluationKernel_exists_nonzero
    (hypersurfaceToBase p hp) e' C j hj hA hsections

end PfaffianDescent.ProjectiveNegativeTwist

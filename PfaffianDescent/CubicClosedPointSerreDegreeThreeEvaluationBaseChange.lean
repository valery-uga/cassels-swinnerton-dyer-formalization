import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationNative
import PfaffianDescent.VoisinFiniteFreeAffineCoverFromLocal

/-! # Actual global sections of the original Serre extension after field extension -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Scalar extension preserves the number of actual global sections of the
original native extension. The literal base-change map is proved bijective
using the constructed actual affine rank-two trivializations. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationBaseChange_finrank_eq
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
    (F : Type u) [Field F] [Algebra K F] :
    Module.finrank F (SchemeModuleGlobalSectionsOver
      (schemeFieldBaseChangeToField (L := F) (hypersurfaceToBase p hp))
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := F) (hypersurfaceToBase p hp))).obj
          (show (hypersurface p hp).Modules from e.E))) =
      Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
        (show (hypersurface p hp).Modules from e.E)) := by
  classical
  letI : Infinite K := CharZero.infinite K
  letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
    schemeModules_hasExt _
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : CompactSpace (hypersurface p hp) :=
    QuasiCompact.compactSpace_of_compactSpace (hypersurfaceToBase p hp)
  have hnine := cubicClosedPointSerreSection_finrank_ge_nine K p hp hp0 i hi hL e
  letI : FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E)) :=
    Module.finite_of_finrank_pos (by omega)
  have hlocal := cubicClosedPointSerreFreeNeighborhood_native_exists_pointwise K p hp hp0 i e hne
  have hbij := globalSectionsFieldBaseChangeLinearMap_bijective_of_localTrivializations
    (L := F) (hypersurfaceToBase p hp) (show (hypersurface p hp).Modules from e.E)
    (ULift.{u} (Fin 2)) hlocal
  let q := schemeModuleGlobalSectionsFieldBaseChangeLinearEquiv
    (L := F) (hypersurfaceToBase p hp) (show (hypersurface p hp).Modules from e.E) hbij
  rw [← q.finrank_eq, Module.finrank_baseChange]

end PfaffianDescent.ProjectiveNegativeTwist

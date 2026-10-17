import PfaffianDescent.CorayOwnCoordinatePositiveNativeKernel
import PfaffianDescent.CorayOwnCoordinateCanonicalCutMapEpi

/-! SOURCE ONLY. The ORIGINAL canonical positive-coordinate cokernel
comparison is IsIso: genuine native kernel equality plus derived Epi.
The WHOLE coordinate cut, all maps and all intrinsic twists are retained. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal original coordinate restriction sequence. Its zero square
is the already proved equality of the SAME native sheaf morphisms. -/
def ownCoordinatePositiveRestrictionSequence
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) : ShortComplex (scheme C).Modules :=
  ShortComplex.mk (ownPositiveCoordinateMultiplication C j m)
    (ownCoordinateCutPositiveRestriction C j m)
    (ownCoordinateCutPositiveRestriction_comp_coordinate_zero C j m)

/-- Native stalk kernel equality reflects to exactness of the actual
sheaf-module short complex, without supplied local exactness. -/
theorem ownCoordinatePositiveRestrictionSequence_exact
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) : (ownCoordinatePositiveRestrictionSequence C j m).Exact := by
  let S := ownCoordinatePositiveRestrictionSequence C j m
  let T := SheafOfModules.toSheaf.{u} (scheme C).ringCatSheaf
  letI : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (scheme C) x)).Exact
  exact (ShortComplex.ab_exact_iff_function_exact _).mpr
    (ownCoordinateCutPositiveRestriction_stalk_exact C j m x)

/-- The ORIGINAL canonical cokernel.desc comparison is invertible. The
target may be nonreduced, the component need not be integral, and no
exactness, invertibility, frame, or rank certificate is an original input. -/
theorem ownCoordinateCokernelToWholeCutPositiveTwist_isIso
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) : IsIso (ownCoordinateCokernelToWholeCutPositiveTwist C j m) := by
  let S := ownCoordinatePositiveRestrictionSequence C j m
  letI : Epi S.g := ownCoordinateCutPositiveRestriction_epi C j m
  have hS : S.Exact := ownCoordinatePositiveRestrictionSequence_exact C j m
  let e : cokernel S.f ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hS.gIsCokernel
  have he : cokernel.π S.f ≫ e.hom = S.g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel S.f) hS.gIsCokernel WalkingParallelPair.one
  have hcanon : ownCoordinateCokernelToWholeCutPositiveTwist C j m = e.hom := by
    apply (cancel_epi (cokernel.π S.f)).mp
    exact (ownCoordinateCokernelToWholeCutPositiveTwist_projection C j m).trans he.symm
  rw [hcanon]
  infer_instance

/-- Actual canonical whole-cut Iso, with its hom definitionally equal to
the ORIGINAL constructed cokernel comparison. -/
def ownCoordinateCokernelWholeCutPositiveTwistIso
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    cokernel (ownPositiveCoordinateMultiplication C j m) ≅
      (Scheme.Modules.pushforward (schemeQuotientMap C
        (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))
        le_sup_left)).obj
        (positiveSheafOfModules (grading
          (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j)))
          (m + 1)) := by
  letI : IsIso (ownCoordinateCokernelToWholeCutPositiveTwist C j m) :=
    ownCoordinateCokernelToWholeCutPositiveTwist_isIso C j m
  exact asIso (ownCoordinateCokernelToWholeCutPositiveTwist C j m)

/-- The whole original cokernel projection is preserved by the actual
canonical Iso; it remains EXACTLY the original graded restriction. -/
theorem ownCoordinateCokernelWholeCutPositiveTwistIso_projection
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j : Fin 4) (m : ℕ) :
    cokernel.π (ownPositiveCoordinateMultiplication C j m) ≫
      (ownCoordinateCokernelWholeCutPositiveTwistIso C j m).hom =
        ownCoordinateCutPositiveRestriction C j m := by
  exact ownCoordinateCokernelToWholeCutPositiveTwist_projection C j m

end PfaffianDescent.Coray
end

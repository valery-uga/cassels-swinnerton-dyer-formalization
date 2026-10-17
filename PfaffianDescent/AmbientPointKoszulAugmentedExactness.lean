import PfaffianDescent.AmbientPointKoszulOffPoint
import PfaffianDescent.AmbientPointAugmentationAtPointExact

/-! # Global exactness of the actual point Koszul augmentation -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The actual final Koszul map and actual point augmentation are exact
on every projective-space stalk. -/
theorem ambientPointKoszul_last_augmentation_stalk_exact (x : Proj PS) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateKoszulLast K))
      ((schemeModuleStalkFunctor (Proj PS) x).map (ambientPointKoszul_augmentation K)) := by
  by_cases hx : x ∈ Set.range (ambientPointKoszul_point K)
  · obtain ⟨k, rfl⟩ := hx
    exact ambientPointAugmentation_last_stalk_exact_at_point K k
  · have hmem : x ∈ ⨆ i : Fin 4, p3StandardOpen (K := K) i := by
      rw [p3StandardOpen_iSup]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
    exact ambientPointKoszul_last_augmentation_stalk_exact_off_range K j x hj hx

set_option backward.isDefEq.respectTransparency false in
/-- The actual final Koszul differential composes to zero with the original
closed-immersion point restriction. -/
theorem ambientPointKoszul_last_augmentation_zero :
    pointGlobalTraceP3CoordinateKoszulLast K ≫ ambientPointKoszul_augmentation K = 0 := by
  apply schemeModule_hom_ext_of_stalkMap_eq
  intro x
  let F := schemeModuleStalkFunctor (Proj PS) x
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  rw [F.map_comp, F.map_zero]
  apply ConcreteCategory.hom_ext
  intro z
  exact (ambientPointKoszul_last_augmentation_stalk_exact K x _).mpr ⟨z, rfl⟩

/-- The actual final differential and actual point augmentation form a short complex. -/
def ambientPointKoszul_lastAugmentationShortComplex : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (pointGlobalTraceP3CoordinateKoszulLast K)
    (ambientPointKoszul_augmentation K) (ambientPointKoszul_last_augmentation_zero K)

set_option backward.isDefEq.respectTransparency false in
/-- Global exactness of the actual augmented final pair. -/
theorem ambientPointKoszul_lastAugmentation_exact :
    (ambientPointKoszul_lastAugmentationShortComplex K).Exact := by
  let S := ambientPointKoszul_lastAugmentationShortComplex K
  let T := SheafOfModules.toSheaf.{u} (Proj PS).ringCatSheaf
  letI : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (Proj PS) x)).Exact
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  exact ambientPointKoszul_last_augmentation_stalk_exact K x

end PfaffianDescent.ProjectiveNegativeTwist

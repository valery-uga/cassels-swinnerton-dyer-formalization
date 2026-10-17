import PfaffianDescent.AmbientPointKoszulBasisOffPoint
import PfaffianDescent.PointGlobalTraceP3BasisAugmentationStalk

/-! # Global exactness of the actual point Koszul augmentation -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)

set_option backward.isDefEq.respectTransparency false in
/-- The actual final Koszul map and actual point augmentation are exact
on every projective-space stalk. -/
theorem ambientPointKoszul_basisLast_augmentation_stalk_exact (x : Proj PS) :
    Function.Exact
      ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisKoszulLast K (ambientPointKoszul_basis M)))
      ((schemeModuleStalkFunctor (Proj PS) x).map (ambientPointKoszul_basisAugmentation M hM)) := by
  by_cases hx : x ∈ Set.range (ambientPointKoszul_basisPoint M hM)
  · obtain ⟨k, rfl⟩ := hx
    exact pointGlobalTraceP3BasisAugmentation_last_stalk_exact_at_point K
      (ambientPointKoszul_basisPoint M hM) (ambientPointKoszul_basis M) 0 k
      (ambientPointKoszul_basisPoint_mem_basicOpen M hM k)
      (ambientPointKoszul_basisPoint_stalk_parameters_span_maximal M hM k)
  · have hmem : x ∈ ⨆ i : Fin 4, Proj.basicOpen PS (ambientPointKoszul_basis M i).val := by
      rw [ambientPointKoszul_basisOpen_iSup M hM]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
    exact ambientPointKoszul_basisLast_augmentation_stalk_exact_off_range M hM j x hj hx

set_option backward.isDefEq.respectTransparency false in
/-- The actual final Koszul differential composes to zero with the original
closed-immersion point restriction. -/
theorem ambientPointKoszul_basisLast_augmentation_zero :
    pointGlobalTraceP3BasisKoszulLast K (ambientPointKoszul_basis M) ≫ ambientPointKoszul_basisAugmentation M hM = 0 := by
  apply schemeModule_hom_ext_of_stalkMap_eq
  intro x
  let F := schemeModuleStalkFunctor (Proj PS) x
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  rw [F.map_comp, F.map_zero]
  apply ConcreteCategory.hom_ext
  intro z
  exact (ambientPointKoszul_basisLast_augmentation_stalk_exact M hM x _).mpr ⟨z, rfl⟩

/-- The actual final differential and actual point augmentation form a short complex. -/
def ambientPointKoszul_basisLastAugmentationShortComplex : ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (pointGlobalTraceP3BasisKoszulLast K (ambientPointKoszul_basis M))
    (ambientPointKoszul_basisAugmentation M hM) (ambientPointKoszul_basisLast_augmentation_zero M hM)

set_option backward.isDefEq.respectTransparency false in
/-- Global exactness of the actual augmented final pair. -/
theorem ambientPointKoszul_basisLastAugmentation_exact :
    (ambientPointKoszul_basisLastAugmentationShortComplex M hM).Exact := by
  let S := ambientPointKoszul_basisLastAugmentationShortComplex M hM
  let T := SheafOfModules.toSheaf.{u} (Proj PS).ringCatSheaf
  letI : T.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (Proj PS) x)).Exact
  apply (ShortComplex.ab_exact_iff_function_exact _).mpr
  exact ambientPointKoszul_basisLast_augmentation_stalk_exact M hM x

end PfaffianDescent.ProjectiveNegativeTwist

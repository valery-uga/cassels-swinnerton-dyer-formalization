import PfaffianDescent.CubicClosedPointSerrePointSplittingSectionEquiv
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationMap

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem pointSplittingSpecSectionCoordinates_apply
    {F A : Type u} [Field F] [Field A] [Algebra F A]
    (I : Type u) [Fintype I] [DecidableEq I]
    (M : (Spec (.of A)).Modules)
    (e : SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅ M)
    (s : SchemeModuleGlobalSectionsOver (Spec.map (CommRingCat.ofHom (algebraMap F A))) M)
    (i : I) :
    pointSplittingSpecSectionCoordinates (F := F) I M e s i =
      (Scheme.ΓSpecIso (.of A)).hom.hom
        (moduleOpenTopLinearEquivOfFreeIso I M e (M.unitHomEquiv s |>.val (op ⊤)) i) := rfl

theorem pointSplittingNativeSpecSectionCoordinates_apply
    {E : Type u} [Field E]
    (I : Type u) [Fintype I] [DecidableEq I]
    (M : (Spec (.of E)).Modules)
    (e : SheafOfModules.free (R := (Spec (.of E)).ringCatSheaf) I ≅ M)
    (v : (moduleSpecΓFunctor (R := CommRingCat.of E)).obj M) (i : I) :
    pointSplittingNativeSpecSectionCoordinates I M e v i =
      (Scheme.ΓSpecIso (.of E)).hom.hom
        (moduleOpenTopLinearEquivOfFreeIso I M e v i) := by
  let a := cubicClosedPointSerreSurfaceJetCotangent_pointNativeGammaOverLinearEquiv
    (Spec.map (CommRingCat.ofHom (algebraMap E E))) rfl M
  let t := a.symm v
  have ht : (M.unitHomEquiv t).val (op ⊤) = v := a.apply_symm_apply v
  change pointSplittingSpecSectionCoordinates (F := E) I M e t i = _
  rw [pointSplittingSpecSectionCoordinates_apply, ht]

theorem pointSplitting_specPoint_over
    {F A E : Type u} [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E]
    (α : A →ₐ[F] E) :
    Spec.map (CommRingCat.ofHom α.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F A)) =
    Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext c
  exact α.commutes c

/-- Under actual pulled free frames the actual component evaluator has the
literal scalar-extension coordinate formula, without a compatibility premise. -/
theorem pointSplitting_component_evaluation_coordinate
    {F A E : Type u} [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E]
    (α : A →ₐ[F] E) (I : Type u) [Fintype I] [DecidableEq I]
    (M : (Spec (.of A)).Modules)
    (e : SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅ M)
    (s : SchemeModuleGlobalSectionsOver (Spec.map (CommRingCat.ofHom (algebraMap F A))) M)
    (i : I) :
    pointSplittingNativeSpecSectionCoordinates I
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom α.toRingHom))).obj M)
      (pullbackFreeIso (Spec.map (CommRingCat.ofHom α.toRingHom)) I e)
      (cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation
        (Spec.map (CommRingCat.ofHom (algebraMap F A)))
        (Spec.map (CommRingCat.ofHom α.toRingHom)) (pointSplitting_specPoint_over α) M s) i =
    α (pointSplittingSpecSectionCoordinates (F := F) I M e s i) := by
  rw [pointSplittingNativeSpecSectionCoordinates_apply,
    cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation_apply,
    pointSplittingSpecSectionCoordinates_apply]
  exact pointSplitting_section_coordinate α.toRingHom I M e (M.unitHomEquiv s) i

end PfaffianDescent

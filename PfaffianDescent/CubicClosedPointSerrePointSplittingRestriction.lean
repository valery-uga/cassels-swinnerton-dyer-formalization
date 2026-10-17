import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationThree

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] isIso_pullbackUnitComparison

/-- Actual finite-subscheme restriction and actual component evaluation
commute through the literal pullback composition isomorphism. -/
theorem pointSplitting_restriction_component_evaluation
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {X D : Scheme.{u}} (base : X ⟶ Spec (.of F)) (d : D ⟶ X)
    (δ : Spec (.of E) ⟶ D)
    (hδ : δ ≫ (d ≫ base) = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (M : X.Modules) (s : SchemeModuleGlobalSectionsOver base M) :
    ((moduleSpecΓFunctor (R := CommRingCat.of E)).map
      ((Scheme.Modules.pullbackComp δ d).inv.app M)).hom
        (cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation base (δ ≫ d)
          (by simpa only [Category.assoc] using hδ) M s) =
    cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation (d ≫ base) δ hδ
      ((Scheme.Modules.pullback d).obj M)
      (cubicClosedPointSerreDegreeThreeEvaluationMap base d M s) := by
  let N := (Scheme.Modules.pullback d).obj M
  have hs : N.unitHomEquiv (cubicClosedPointSerreDegreeThreeEvaluationMap base d M s) =
      pullbackSection d M (isIso_pullbackUnitComparison _) (M.unitHomEquiv s) := by
    apply N.unitHomEquiv.symm.injective
    rw [Equiv.symm_apply_apply, pullbackSection_unitHomEquiv_symm_eq_inv,
      Equiv.symm_apply_apply]
    rfl
  rw [cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation_apply,
    cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation_apply, hs]
  exact congrArg (fun t => t.val (op ⊤))
    (pullbackSection_comp δ d M (isIso_pullbackUnitComparison _)
      (isIso_pullbackUnitComparison _) (isIso_pullbackUnitComparison _) (M.unitHomEquiv s))

end PfaffianDescent

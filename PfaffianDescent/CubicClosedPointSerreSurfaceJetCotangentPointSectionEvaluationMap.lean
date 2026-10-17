import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationAction

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] isIso_pullbackUnitComparison

/-- Actual F-linear global-section evaluation into the restriction of the
ACTUAL native E-module of point-pullback sections. -/
def cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation
    {F E : Type u} [Field F] [Field E] [Algebra F E] {X : Scheme.{u}}
    (base : X ⟶ Spec (CommRingCat.of F)) (r : Spec (CommRingCat.of E) ⟶ X)
    (hr : r ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E))) (M : X.Modules) :
    SchemeModuleGlobalSectionsOver base M →ₗ[F]
      (ModuleCat.restrictScalars (algebraMap F E)).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of E)).obj ((Scheme.Modules.pullback r).obj M)) :=
  (cubicClosedPointSerreSurfaceJetCotangent_pointNativeGammaOverLinearEquiv
    (r ≫ base) hr ((Scheme.Modules.pullback r).obj M)).toLinearMap.comp
    (cubicClosedPointSerreDegreeThreeEvaluationMap base r M)

/-- Evaluation is literally pullbackSection followed by value on the top open. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation_apply
    {F E : Type u} [Field F] [Field E] [Algebra F E] {X : Scheme.{u}}
    (base : X ⟶ Spec (CommRingCat.of F)) (r : Spec (CommRingCat.of E) ⟶ X)
    (hr : r ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E))) (M : X.Modules)
    (s : SchemeModuleGlobalSectionsOver base M) :
    cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation base r hr M s =
      (pullbackSection r M (isIso_pullbackUnitComparison _) (M.unitHomEquiv s)).val (op ⊤) := by
  let N := (Scheme.Modules.pullback r).obj M
  have h : N.unitHomEquiv (cubicClosedPointSerreDegreeThreeEvaluationMap base r M s) =
      pullbackSection r M (isIso_pullbackUnitComparison _) (M.unitHomEquiv s) := by
    apply N.unitHomEquiv.symm.injective
    rw [Equiv.symm_apply_apply, pullbackSection_unitHomEquiv_symm_eq_inv,
      Equiv.symm_apply_apply]
    rfl
  exact congrArg (fun t : N.sections => t.val (op ⊤)) h

/-- Actual native point evaluation commutes with an arbitrary actual module
morphism, in particular the original Serre projection. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation_naturality
    {F E : Type u} [Field F] [Field E] [Algebra F E] {X : Scheme.{u}}
    (base : X ⟶ Spec (CommRingCat.of F)) (r : Spec (CommRingCat.of E) ⟶ X)
    (hr : r ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    {M N : X.Modules} (π : M ⟶ N) (s : SchemeModuleGlobalSectionsOver base M) :
    ((moduleSpecΓFunctor (R := CommRingCat.of E)).map ((Scheme.Modules.pullback r).map π)).hom
      (cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation base r hr M s) =
    cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation base r hr N
      (schemeModuleGlobalSectionsMap base π s) := by
  change (inv (pullbackUnitComparison r) ≫ (Scheme.Modules.pullback r).map s ≫
    (Scheme.Modules.pullback r).map π).val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of E), ⊤)) =
    (inv (pullbackUnitComparison r) ≫ (Scheme.Modules.pullback r).map (s ≫ π)).val.app
      (op ⊤) (1 : Γ(Spec (CommRingCat.of E), ⊤))
  rw [Functor.map_comp]

end PfaffianDescent

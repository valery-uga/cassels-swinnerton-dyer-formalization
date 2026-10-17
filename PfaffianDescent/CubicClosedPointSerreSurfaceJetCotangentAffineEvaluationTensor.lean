import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineEvaluationUnit

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The ACTUAL affine sheaf evaluation map, with native Gamma comparison, becomes
exactly the scalar-extension unit after taking the actual fibre coordinate. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineEvaluation_tensor_unit
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) :
    (tilde.toTildeΓNatIso (R := R)).hom.app M ≫
      (moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          ((tilde.functor R).obj M)) ≫
      (affineGammaPushforwardNatIso φ).hom.app
        ((Scheme.Modules.pullback (Spec.map φ)).obj ((tilde.functor R).obj M)) ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((moduleSpecΓFunctor (R := S)).map ((affineTildePullbackNatIso φ).hom.app M) ≫
          (tilde.toTildeΓNatIso (R := S)).inv.app
            ((ModuleCat.extendScalars φ.hom).obj M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M := by
  let q := (ModuleCat.restrictScalars φ.hom).map
    ((tilde.toTildeΓNatIso (R := S)).inv.app ((ModuleCat.extendScalars φ.hom).obj M))
  have h := congrArg (fun f => f ≫ q)
    (cubicClosedPointSerreSurfaceJetCotangent_affineEvaluation_unit φ M)
  have hc :
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((tilde.toTildeΓNatIso (R := S)).hom.app ((ModuleCat.extendScalars φ.hom).obj M))) ≫ q =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M := by
    dsimp only [q]
    rw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  simpa only [q, Functor.map_comp, Functor.comp_map, Category.assoc] using h.trans hc

end PfaffianDescent

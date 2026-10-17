import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentFiber

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal sheaf pullback unit becomes the literal scalar-extension unit
under the native affine Gamma comparisons. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineEvaluation_unit
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) :
    (tilde.toTildeΓNatIso (R := R)).hom.app M ≫
      (moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          ((tilde.functor R).obj M)) ≫
      (affineGammaPushforwardNatIso φ).hom.app
        ((Scheme.Modules.pullback (Spec.map φ)).obj ((tilde.functor R).obj M)) ≫
      (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).map
        ((affineTildePullbackNatIso φ).hom.app M) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.toTildeΓNatIso (R := S)).hom.app
          ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h := affineTildePullbackNatIso_homEquiv φ M
  dsimp only at h
  rw [Adjunction.homEquiv_unit] at h
  exact h

end PfaffianDescent

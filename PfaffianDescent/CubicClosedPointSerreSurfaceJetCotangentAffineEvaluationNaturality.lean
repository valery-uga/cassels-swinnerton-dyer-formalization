import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineEvaluationApply

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual point evaluation on actual affine module sections, before any tilde coordinate. -/
def cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules) :
    (moduleSpecΓFunctor (R := R)).obj M ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj M)) :=
  (moduleSpecΓFunctor (R := R)).map
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
      (affineGammaPushforwardNatIso φ).hom.app _

/-- Actual section evaluation commutes with every actual module map, including
native chart ideal and twist comparisons. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation_naturality
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {M N : (Spec R).Modules} (f : M ⟶ N) :
    (moduleSpecΓFunctor (R := R)).map f ≫
      cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation φ N =
    cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation φ M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((moduleSpecΓFunctor (R := S)).map ((Scheme.Modules.pullback (Spec.map φ)).map f)) := by
  let P := Scheme.Modules.pullback (Spec.map φ)
  let Q := Scheme.Modules.pushforward (Spec.map φ)
  let G := moduleSpecΓFunctor (R := R)
  have hu := congrArg (fun t => G.map t)
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality f)
  simp only [Functor.map_comp] at hu
  have hn := (affineGammaPushforwardNatIso φ).hom.naturality (P.map f)
  simp only [Functor.comp_map, Functor.id_map] at hu hn
  unfold cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
  calc
    _ = (G.map ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
      G.map (Q.map (P.map f))) ≫ (affineGammaPushforwardNatIso φ).hom.app (P.obj N) := by
        rw [← Category.assoc]
        exact congrArg (fun t => t ≫ (affineGammaPushforwardNatIso φ).hom.app (P.obj N)) hu
    _ = _ := by
      simp only [Category.assoc]
      rw [hn]

end PfaffianDescent

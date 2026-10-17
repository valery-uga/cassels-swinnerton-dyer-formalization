import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackTensorMap
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPushforwardTensorNaturality
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' N N' : Y.Modules}
    (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (schemeModuleTensorMap a b) ≫
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M' N' =
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M N ≫
      schemeModuleTensorMap ((Scheme.Modules.pullback f).map a)
        ((Scheme.Modules.pullback f).map b) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let P := Scheme.Modules.pullback f
  let G := Scheme.Modules.pushforward f
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap, adj,
    Equiv.apply_symm_apply]
  change schemeModuleTensorMap a b ≫
      (schemeModuleTensorMap (adj.unit.app M') (adj.unit.app N') ≫
        cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f (P.obj M') (P.obj N')) =
    (schemeModuleTensorMap (adj.unit.app M) (adj.unit.app N) ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f (P.obj M) (P.obj N)) ≫
        G.map (schemeModuleTensorMap (P.map a) (P.map b))
  have hη : schemeModuleTensorMap a b ≫
      schemeModuleTensorMap (adj.unit.app M') (adj.unit.app N') =
    schemeModuleTensorMap (adj.unit.app M) (adj.unit.app N) ≫
      schemeModuleTensorMap (G.map (P.map a)) (G.map (P.map b)) := by
    rw [schemeModuleTensorMap_comp, schemeModuleTensorMap_comp]
    have ha : a ≫ adj.unit.app M' = adj.unit.app M ≫ G.map (P.map a) :=
      adj.unit.naturality a
    have hb : b ≫ adj.unit.app N' = adj.unit.app N ≫ G.map (P.map b) :=
      adj.unit.naturality b
    rw [ha,hb]
  rw [← Category.assoc, hη, Category.assoc,
    cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap_naturality,
    Category.assoc]
end PfaffianDescent

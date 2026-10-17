import PfaffianDescent.ActualPushforwardTensorLocalSectionAction
import PfaffianDescent.ActualPointLocalAdjunctionSectionEvaluation

/- SOURCE ONLY / UNVERIFIED. The TRUE point pullback tensor comparison
sends the LOCAL class of a pure tensor to the actual tensor of its SAME
local point classes. Derived from both actual adjunctions, no coefficient
or generator-comparison premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

lemma actualPointLocalTensorPullbackAction
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M N : X.Modules)
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleSpecΓFunctor (R := .of L)).map
      (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q M N)
      (actualPointLocalSectionClass q (schemeModuleTensor M N) U hU
        (actualModuleLocalTensorSection M N U m n)) =
    actualModuleLocalTensorSection ((Scheme.Modules.pullback q).obj M)
      ((Scheme.Modules.pullback q).obj N) ⊤
      (actualPointLocalSectionClass q M U hU m)
      (actualPointLocalSectionClass q N U hU n) := by
  rw [actualPointLocalAdjunctionSectionEvaluation]
  let P := Scheme.Modules.pullback q
  let adj := Scheme.Modules.pullbackPushforwardAdjunction q
  let T := schemeModuleTensor (P.obj M) (P.obj N)
  let t := eqToHom (congrArg op hU)
  have hAdj : adj.homEquiv (schemeModuleTensor M N) T
      (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q M N) =
      schemeModuleTensorMap (adj.unit.app M) (adj.unit.app N) ≫
        cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap q (P.obj M) (P.obj N) :=
    (adj.homEquiv (schemeModuleTensor M N) T).apply_symm_apply
      (schemeModuleTensorMap (adj.unit.app M) (adj.unit.app N) ≫
        cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap q (P.obj M) (P.obj N))
  rw [hAdj]
  change T.val.map t
    ((schemeModuleTensorMap (adj.unit.app M) (adj.unit.app N) ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap q (P.obj M) (P.obj N)).val.app
      (op U) (actualModuleLocalTensorSection M N U m n)) = _
  change T.val.map t
    ((cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap q (P.obj M) (P.obj N)).val.app
      (op U) ((schemeModuleTensorMap (adj.unit.app M) (adj.unit.app N)).val.app
        (op U) (actualModuleLocalTensorSection M N U m n))) = _
  have hn := actualModuleLocalTensorSection_naturality
    (adj.unit.app M) (adj.unit.app N) U m n
  have hp := actualPushforwardTensorMap_localSection q (P.obj M) (P.obj N) U
    ((adj.unit.app M).val.app (op U) m) ((adj.unit.app N).val.app (op U) n)
  have hr := actualModuleLocalTensorSection_restrict (P.obj M) (P.obj N) t
    ((adj.unit.app M).val.app (op U) m) ((adj.unit.app N).val.app (op U) n)
  exact (congrArg (fun z => T.val.map t
    ((cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap q
      (P.obj M) (P.obj N)).val.app (op U) z)) hn).trans
    ((congrArg (fun z => T.val.map t z) hp).trans hr)

end PfaffianDescent

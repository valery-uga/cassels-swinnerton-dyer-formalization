import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackTensorUnit
import PfaffianDescent.ActualPointLocalTensorUnitContraction
import PfaffianDescent.ActualPointLocalSectionClassNaturality

/-! SOURCE ONLY / UNVERIFIED. Actual local class scalar compatibility is
derived by the SAME genuine unit pullback/tensor/right-unit square. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualPointLocalSectionClass_scalar
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤)
    (r : Γ(X, U)) (w : M.val.obj (op U)) :
    actualPointLocalSectionClass q M U hU (r • w) =
      (show Γ(Spec (.of L), ⊤) from
        (pullbackUnitComparison q).val.app (op ⊤)
          (actualPointLocalSectionClass q
            (SheafOfModules.unit X.ringCatSheaf) U hU r)) •
      (show ((Scheme.Modules.pullback q).obj M).val.obj (op ⊤) from
        actualPointLocalSectionClass q M U hU w) := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let P := Scheme.Modules.pullback q
  let u := pullbackUnitComparison q
  letI : IsIso u := isIso_pullbackUnitComparison q
  have hlocal := actualPointLocalTensorUnitContraction q M O U hU (asIso u) w r
  have hd : cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q M O ≫
      (actualPointTwistUntwistIso (P.obj M) (P.obj O) (asIso u)).hom =
      P.map (schemeModuleTensorUnitRightIso M).hom :=
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_unit_right q M
  have hn := actualPointLocalSectionClass_naturality q
    (schemeModuleTensorUnitRightIso M).hom U hU
    (actualModuleLocalTensorSection M O U w r)
  have hr := actualModuleLocalTensorRightUnitAction M U w r
  have hn' : (moduleSpecΓFunctor (R := .of L)).map
      (P.map (schemeModuleTensorUnitRightIso M).hom)
      (actualPointLocalSectionClass q (schemeModuleTensor M O) U hU
        (actualModuleLocalTensorSection M O U w r)) =
      actualPointLocalSectionClass q M U hU (r • w) :=
    hn.trans (congrArg (actualPointLocalSectionClass q M U hU) hr)
  rw [hd] at hlocal
  exact hn'.symm.trans hlocal

end PfaffianDescent

import PfaffianDescent.ActualPointLocalTensorUnitContraction

/- SOURCE ONLY / UNVERIFIED. The local O2 contraction coefficient is
computed in the ACTUAL residue field, by the genuine Gamma-Spec scalar
map. No assertion that arbitrary residue scaling preserves a fixed trace
functional or that a native generator coefficient is 1. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualFieldGammaScalar_eq_residueScalar
    {L : Type u} [Field L] (M : (Spec (.of L)).Modules)
    (c : Γ(Spec (.of L), ⊤)) (m : (moduleSpecΓFunctor (R := .of L)).obj M) :
    c • (show Γ(M, ⊤) from m) =
      (Scheme.ΓSpecIso (.of L)).hom.hom c • m := by
  let y : Γ(M, ⊤) := m
  have h := Scheme.Modules.smul_Spec_def
    (R := CommRingCat.of L) (M := M) (U := ⊤)
    ((Scheme.ΓSpecIso (.of L)).hom.hom c) y
  change (Scheme.ΓSpecIso (.of L)).hom.hom c • m =
    ((Spec (.of L)).presheaf.map (𝟙 (op ⊤))
      ((Scheme.ΓSpecIso (.of L)).inv.hom ((Scheme.ΓSpecIso (.of L)).hom.hom c))) • y at h
  rw [Iso.hom_inv_id_apply,
    CategoryTheory.Functor.map_id ((Spec (.of L)).presheaf) (op ⊤)] at h
  exact h.symm

lemma actualPointLocalTensorResidueCoefficient
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M T : X.Modules)
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤)
    (e : (Scheme.Modules.pullback q).obj T ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (m : M.val.obj (op U)) (t : T.val.obj (op U)) :
    (moduleSpecΓFunctor (R := .of L)).map
      (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q M T ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj M)
          ((Scheme.Modules.pullback q).obj T) e).hom)
      (actualPointLocalSectionClass q (schemeModuleTensor M T) U hU
        (actualModuleLocalTensorSection M T U m t)) =
    (Scheme.ΓSpecIso (.of L)).hom.hom
      (e.hom.val.app (op ⊤) (actualPointLocalSectionClass q T U hU t)) •
        actualPointLocalSectionClass q M U hU m := by
  rw [actualPointLocalTensorUnitContraction]
  exact actualFieldGammaScalar_eq_residueScalar ((Scheme.Modules.pullback q).obj M) _ _

end PfaffianDescent

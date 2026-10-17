import PfaffianDescent.SchemeModuleTensor

/- SOURCE ONLY / UNVERIFIED. Actual LOCAL tensor sections are the image
of pure tensors under genuine module sheafification, preserving actual
restriction and module-map naturality. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def actualModuleLocalTensorSection {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (schemeModuleTensor M N).val.obj (op U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app (op U)
      (m ⊗ₜ[Γ(X, U)] n)

lemma actualModuleLocalTensorSection_naturality {X : Scheme.{u}}
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N')
    (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (schemeModuleTensorMap a b).val.app (op U)
      (actualModuleLocalTensorSection M N U m n) =
    actualModuleLocalTensorSection M' N' U
      (a.val.app (op U) m) (b.val.app (op U) n) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let t := PresheafOfModules.Monoidal.tensorHom a.val b.val
  have h := congrArg (fun v => v.app (op U) (m ⊗ₜ[Γ(X, U)] n))
    (adj.unit.naturality t)
  exact h.symm

lemma actualModuleLocalTensorSection_restrict {X : Scheme.{u}} (M N : X.Modules)
    {U V : X.Opens} (t : op U ⟶ op V)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (schemeModuleTensor M N).val.map t (actualModuleLocalTensorSection M N U m n) =
      actualModuleLocalTensorSection M N V (M.val.map t m) (N.val.map t n) := by
  let P := PresheafOfModules.Monoidal.tensorObj M.val N.val
  let eta := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have h := ConcreteCategory.congr_hom (eta.naturality t) (m ⊗ₜ[Γ(X, U)] n)
  change eta.app (op V) (P.map t (m ⊗ₜ[Γ(X, U)] n)) =
    (schemeModuleTensor M N).val.map t
      (eta.app (op U) (m ⊗ₜ[Γ(X, U)] n)) at h
  exact h.symm

end PfaffianDescent

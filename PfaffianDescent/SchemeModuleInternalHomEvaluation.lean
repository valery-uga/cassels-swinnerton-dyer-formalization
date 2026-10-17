import PfaffianDescent.SchemeModuleInternalHomOverSections
import PfaffianDescent.SchemeModuleTensor

/-! Actual canonical evaluation of the CONSTRUCTED O-linear Hom sheaf.
The raw pairing sends m tensor a to the literal value a_U(m); it is
natural for ORIGINAL restrictions and descends by actual sheafification.
An inverse/pole claim still requires the local rank-one IsIso integration.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (M N : X.Modules)

/-- The ORIGINAL-ring bilinear pairing on actual sections. Both scalar
laws are proved from actual local linearity and actual coefficient
restriction, independently of any chart or comparison equivalence. -/
def evaluationBilinear (U : X.Opens) :
    M.val.obj (op U) →ₗ[Γ(X, U)]
      (sheaf M N).val.obj (op U) →ₗ[Γ(X, U)] N.val.obj (op U) where
  toFun m :=
    { toFun := fun a => a.1.app (op (Over.mk (𝟙 U))) m
      map_add' := by intro a b; rfl
      map_smul' := by
        intro r a
        let s : Γ(N, U) := a.1.app (op (Over.mk (𝟙 U))) m
        change (X.presheaf.map (𝟙 U).op r : Γ(X, U)) • s = r • s
        exact congrArg (fun c : Γ(X, U) => c • s)
          (ConcreteCategory.congr_hom (X.presheaf.map_id (op U)) r) }
  map_add' := by
    intro m n
    apply LinearMap.ext
    intro a
    exact (a.1.app (op (Over.mk (𝟙 U)))).hom.map_add m n
  map_smul' := by
    intro r m
    apply LinearMap.ext
    intro a
    exact a.2 (Over.mk (𝟙 U)) r m

/-- The pairing is literal component evaluation. -/
theorem evaluationBilinear_apply (U : X.Opens) (m : M.val.obj (op U))
    (a : (sheaf M N).val.obj (op U)) :
    evaluationBilinear M N U m a = a.1.app (op (Over.mk (𝟙 U))) m := rfl

/-- Genuine compatibility of evaluation with ACTUAL restriction maps. -/
theorem evaluationBilinear_restrict {U V : X.Opens} (f : V ⟶ U)
    (m : M.val.obj (op U)) (a : (sheaf M N).val.obj (op U)) :
    N.val.map f.op (evaluationBilinear M N U m a) =
      evaluationBilinear M N V (M.val.map f.op m) ((sheaf M N).val.map f.op a) := by
  change N.val.map f.op (a.1.app (op (Over.mk (𝟙 U))) m) =
    ((CategoryTheory.presheafHom M.presheaf N.presheaf).map f.op a.1).app
      (op (Over.mk (𝟙 V))) (M.val.map f.op m)
  let z : Over.mk f ⟶ Over.mk (𝟙 U) := Over.homMk f
  have hcomponent := CategoryTheory.presheafHom_map_app_op_mk_id
    (F := M.presheaf) (G := N.presheaf) f a.1
  exact ((ConcreteCategory.congr_hom (a.1.naturality z.op) m).symm).trans
    (ConcreteCategory.congr_hom hcomponent (M.val.map f.op m)).symm

/-- The actual presheaf tensor evaluation, with naturality internally
derived from the SAME original additive/component restriction law. -/
def evaluationPresheaf :
    PresheafOfModules.Monoidal.tensorObj M.val (sheaf M N).val ⟶ N.val where
  app U := ModuleCat.ofHom (TensorProduct.lift (evaluationBilinear M N U.unop))
  naturality := by
    intro U V f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m a
    change (TensorProduct.lift (evaluationBilinear M N V.unop))
        ((PresheafOfModules.Monoidal.tensorObj M.val (sheaf M N).val).map f
          (m ⊗ₜ[Γ(X, U.unop)] a)) =
      N.val.map f ((TensorProduct.lift (evaluationBilinear M N U.unop))
        (m ⊗ₜ[Γ(X, U.unop)] a))
    have htensor :
        (PresheafOfModules.Monoidal.tensorObj M.val (sheaf M N).val).map f
            (m ⊗ₜ[Γ(X, U.unop)] a) =
          (M.val.map f m) ⊗ₜ[Γ(X, V.unop)] ((sheaf M N).val.map f a) :=
      PresheafOfModules.Monoidal.tensorObj_map_tmul
        (R := X.presheaf) (M₁ := M.val) (M₂ := (sheaf M N).val) f m a
    exact (congrArg (TensorProduct.lift (evaluationBilinear M N V.unop)) htensor).trans
      ((evaluationBilinear_restrict M N f.unop m a).symm)

/-- Actual raw evaluation value on a pure tensor. -/
theorem evaluationPresheaf_apply (U : X.Opens) (m : M.val.obj (op U))
    (a : (sheaf M N).val.obj (op U)) :
    (evaluationPresheaf M N).app (op U) (m ⊗ₜ[Γ(X, U)] a) =
      a.1.app (op (Over.mk (𝟙 U))) m := rfl

/-- GLOBAL canonical evaluation on the ACTUAL constructed Hom module
sheaf and ACTUAL sheafified tensor product. The module sheaf already
satisfies the sheaf axiom; only the tensor product is sheafified here. -/
def evaluation : schemeModuleTensor M (sheaf M N) ⟶ N :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
    (evaluationPresheaf M N)

/-- The GLOBAL map descends the SAME literal raw evaluation. -/
theorem evaluation_raw :
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _)
      (evaluation M N) = evaluationPresheaf M N := by
  exact Equiv.apply_symm_apply _ _

/-- GLOBAL evaluation for the actual O-linear dual of the SAME input
module. No invertibility certificate or positive pole claim is included. -/
def dualEvaluation : schemeModuleTensor M (dual M) ⟶ SheafOfModules.unit X.ringCatSheaf :=
  evaluation M (SheafOfModules.unit X.ringCatSheaf)

end PfaffianDescent.SchemeModuleInternalHom

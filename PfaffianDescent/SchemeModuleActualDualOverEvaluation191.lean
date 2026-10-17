import PfaffianDescent.SchemeModuleInternalHomIncrementChartCokernel
import PfaffianDescent.SchemeModuleCanonicalTensorFieldMultiplication

/-! Source-only191. The ACTUAL canonical sheafified evaluation is the
actual tensor of the original frame and the internally constructed dual
coefficient chart. No evaluation-square or generation premise is supplied. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}} (M : X.Modules)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual over-unit carrier is definitionally the ORIGINAL section ring.
This local instance exposes that existing ring without changing any chart. -/
local instance actualOverUnitSectionCommRing191 (U : X.Opens) (V : (Over U)ᵒᵖ) :
    CommRing (((SheafOfModules.unit X.ringCatSheaf).over U).val.obj V) :=
  (show CommRing (Γ(X, V.unop.left)) from inferInstance)

/-- Original sheafification unit and adjunction give the SAME literal
section evaluation on the actual sheafified pure tensor. -/
theorem actualDualEvaluation_pureSection191
    (U : X.Opens) (m : M.val.obj (op U)) (a : (dual M).val.obj (op U)) :
    (dualEvaluation M).val.app (op U)
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M (dual M) (op U) m a) =
      evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) U m a := by
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let T := PresheafOfModules.Monoidal.tensorObj M.val (dual M).val
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h : A.unit.app T ≫ (dualEvaluation M).val = evaluationPresheaf M O := by
    have hr := evaluation_raw M O
    change A.unit.app T ≫ (dualEvaluation M).val = evaluationPresheaf M O at hr
    exact hr
  have hv := congrArg (fun k => (k.app (op U)).hom (m ⊗ₜ[Γ(X, U)] a)) h
  change (dualEvaluation M).val.app (op U)
      (SheafOfModules.commRingSheafTensorPureSection X.sheaf M (dual M) (op U) m a) =
    evaluationBilinear M O U m a at hv
  exact hv

/-- On EVERY smaller open in the ORIGINAL chart, actual evaluation is
multiplication of the original frame coordinate and actual dual coefficient. -/
theorem actualDualOverCoefficient_evaluation191
    (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (V : (Over U)ᵒᵖ) (m : M.val.obj (op V.unop.left))
    (a : (dual M).val.obj (op V.unop.left)) :
    evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V.unop.left m a =
      e.hom.val.app V m * (dualOverUnitIso U e).hom.val.app V a := by
  let q : M.val.obj (op V.unop.left) ≃ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) :=
    ((SheafOfModules.evaluation (X.ringCatSheaf.over U) V).mapIso e).toLinearEquiv
  have hm : m = q m • q.symm (1 : Γ(X, V.unop.left)) := by
    apply q.injective
    rw [q.map_smul, q.apply_symm_apply, smul_eq_mul, mul_one]
  have hd : (dualOverUnitIso U e).hom.val.app V a =
      evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V.unop.left
        (q.symm (1 : Γ(X, V.unop.left))) a := by
    rw [dualOverUnitIso_hom_val]
    rfl
  calc
    _ = evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V.unop.left
        (q m • q.symm (1 : Γ(X, V.unop.left))) a :=
      congrArg (fun z => evaluationBilinear M
        (SheafOfModules.unit X.ringCatSheaf) V.unop.left z a) hm
    _ = q m • evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V.unop.left
        (q.symm (1 : Γ(X, V.unop.left))) a :=
      ((evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V.unop.left).flip a).map_smul _ _
    _ = _ := by
      change @HMul.hMul (Γ(X, V.unop.left)) (Γ(X, V.unop.left))
        (Γ(X, V.unop.left)) inferInstance (q m)
        (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf)
          V.unop.left (q.symm (1 : Γ(X, V.unop.left))) a) =
        @HMul.hMul (Γ(X, V.unop.left)) (Γ(X, V.unop.left))
          (Γ(X, V.unop.left)) inferInstance (e.hom.val.app V m)
          ((dualOverUnitIso U e).hom.val.app V a)
      exact congrArg (fun r : Γ(X, V.unop.left) =>
        @HMul.hMul (Γ(X, V.unop.left)) (Γ(X, V.unop.left))
          (Γ(X, V.unop.left)) inferInstance (q m) r) hd.symm

/-- Native over-site tensor comparison and actual unit counit give the
original product coefficient on every smaller-open pure section. -/
theorem actualTensorOverUnitIso_pureComponent191
    (N : X.Modules) (U : X.Opens)
    (eM : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (eN : N.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (V : (Over U)ᵒᵖ) (m : M.val.obj (op V.unop.left))
    (n : N.val.obj (op V.unop.left)) :
    (schemeModuleTensorOverUnitIso M N U eM eN).hom.val.app V
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N
          (op V.unop.left) m n) =
      eM.hom.val.app V m * eN.hom.val.app V n := by
  change (SheafOfModules.commRingSheafTensorCanonicalUnitIso
      (SheafOfModules.commRingSheafOver X.sheaf U) eM eN).hom.val.app V
      ((schemeModuleTensorOverIso U M N).hom.val.app V
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M N
          (op V.unop.left) m n)) = _
  rw [schemeModuleTensorOverIso_pureSection]
  exact SheafOfModules.commRingSheafTensorCanonicalUnitIso_pureSection
    (SheafOfModules.commRingSheafOver X.sheaf U) eM eN V m n

/-- The WHOLE actual over-site evaluation map equals the genuine tensor
chart. Every actual section is shown to be pure using the internally
constructed tensor/dual charts; no section-generation certificate is input. -/
theorem actualDualEvaluation_over_eq_tensorChart191
    (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (dualEvaluation M).over U =
      (schemeModuleTensorOverUnitIso M (dual M) U e (dualOverUnitIso U e)).hom := by
  let d := dualOverUnitIso U e
  let t := schemeModuleTensorOverUnitIso M (dual M) U e d
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let F := SheafOfModules.evaluation (X.ringCatSheaf.over U) V
  let qM : M.val.obj (op V.unop.left) ≃ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) :=
    (F.mapIso e).toLinearEquiv
  let qD : (dual M).val.obj (op V.unop.left) ≃ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) :=
    (F.mapIso d).toLinearEquiv
  let qT : (schemeModuleTensor M (dual M)).val.obj (op V.unop.left)
      ≃ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) :=
    (F.mapIso t).toLinearEquiv
  let m := qM.symm (qT s)
  let a := qD.symm (1 : Γ(X, V.unop.left))
  have hpure : SheafOfModules.commRingSheafTensorPureSection X.sheaf M (dual M)
      (op V.unop.left) m a = s := by
    apply qT.injective
    change t.hom.val.app V
        (SheafOfModules.commRingSheafTensorPureSection X.sheaf M (dual M)
          (op V.unop.left) m a) = qT s
    rw [actualTensorOverUnitIso_pureComponent191]
    change qM (qM.symm (qT s)) * qD (qD.symm (1 : Γ(X, V.unop.left))) = qT s
    rw [qM.apply_symm_apply, qD.apply_symm_apply, mul_one]
  rw [← hpure]
  exact (actualDualEvaluation_pureSection191 M V.unop.left m a).trans
    ((actualDualOverCoefficient_evaluation191 M U e V m a).trans
      (actualTensorOverUnitIso_pureComponent191 M (dual M) U e d V m a).symm)

end PfaffianDescent.SchemeModuleInternalHom

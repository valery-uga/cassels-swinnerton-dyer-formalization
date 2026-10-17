import PfaffianDescent.SchemeModuleInternalHomIncrementCoefficient

/-! Actual rank-one dual evaluation commutes with the SAME inclusion's
canonical Hom section. This is proved locally from original frames,
then globally by the actual constructed dual's sheaf separation. The
result is a GLOBAL equality of the original sheafified tensor maps;
no evaluation/action compatibility certificate is assumed.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {M : X.Modules}

/-- On a genuine original rank-one chart, the SAME canonical dual
increment applied to evaluation equals the SAME inclusion coefficient
acting on the original dual section. No regularity premise is needed. -/
theorem rankOneEvaluation_unitToHom_apply
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (m : M.val.obj (op U)) (a : (dual M).val.obj (op U)) :
    (unitToHom j).val.app (op U)
        (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) U m a) =
      j.val.app (op U) m • a := by
  let q := overTopLinearEquiv M U e
  let a₀ := localUnitSection M U e
  let c : Γ(X, U) := a.1.app (op (Over.mk (𝟙 U))) (q.symm 1)
  let z : Γ(X, U) := j.val.app (op U) (q.symm 1)
  have ha : a = c • a₀ := section_eq_coefficient_smul M U e a
  have hj : homSection j U = z • a₀ := section_eq_coefficient_smul M U e (homSection j U)
  have hm : m = q m • q.symm 1 := by
    apply q.injective
    rw [q.map_smul, q.apply_symm_apply, smul_eq_mul, mul_one]
  have hjm : j.val.app (op U) m = q m * z := by
    calc
      _ = j.val.app (op U) (q m • q.symm 1) := congrArg (j.val.app (op U)) hm
      _ = q m • j.val.app (op U) (q.symm 1) := (j.val.app (op U)).hom.map_smul _ _
      _ = _ := rfl
  have hev : evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) U m a =
      c * q m := by
    rw [ha, (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) U m).map_smul]
    rfl
  calc
    _ = (c * q m) • (z • a₀) := by rw [unitToHom_apply, hev, hj]
    _ = ((c * q m) * z) • a₀ := (mul_smul _ _ _).symm
    _ = ((q m * z) * c) • a₀ := congrArg (fun r : Γ(X, U) => r • a₀)
      ((mul_assoc c (q m) z).trans (mul_comm c (q m * z)))
    _ = j.val.app (op U) m • a := by rw [hjm, ha, mul_smul]

/-- Actual restriction and sheaf separation extend the same rank-one
identity to EVERY open, even when the original ideal has no global frame.
Only natural original-M charts occur as generic hypotheses. -/
theorem rankOneEvaluation_unitToHom_apply_of_pointwise_unitCharts
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, M.over (B x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (W : X.Opens) (m : M.val.obj (op W)) (a : (dual M).val.obj (op W)) :
    (unitToHom j).val.app (op W)
        (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) W m a) =
      j.val.app (op W) m • a := by
  apply (dual M).isSheaf.section_ext
  intro x hxW
  let V : X.Opens := W ⊓ B x
  let f : V ⟶ W := homOfLE inf_le_left
  let g : V ⟶ B x := homOfLE inf_le_right
  let eV := overUnitChartRestrict M g (eB x)
  refine ⟨V, inf_le_left, ⟨hxW, hB x⟩, ?_⟩
  calc
    _ = (unitToHom j).val.app (op V)
        (X.presheaf.map f.op
          (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) W m a)) :=
      (PresheafOfModules.naturality_apply (unitToHom j).val f.op _).symm
    _ = (unitToHom j).val.app (op V)
        (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V
          (M.val.map f.op m) ((dual M).val.map f.op a)) :=
      congrArg ((unitToHom j).val.app (op V))
        (evaluationBilinear_restrict M (SheafOfModules.unit X.ringCatSheaf) f m a)
    _ = j.val.app (op V) (M.val.map f.op m) • (dual M).val.map f.op a :=
      rankOneEvaluation_unitToHom_apply j V eV _ _
    _ = X.presheaf.map f.op (j.val.app (op W) m) • (dual M).val.map f.op a :=
      congrArg (fun r : Γ(X, V) => r • (dual M).val.map f.op a)
        (PresheafOfModules.naturality_apply j.val f.op m)
    _ = _ := ((dual M).val.map_smul f.op (j.val.app (op W) m) a).symm

/-- The ORIGINAL raw tensor identity on actual presheaves, derived from
the original scalar action and the local geometric rank-one identity. -/
theorem rankOneEvaluation_presheaf_action_of_pointwise_unitCharts
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, M.over (B x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (B x)) :
    evaluationPresheaf M (SheafOfModules.unit X.ringCatSheaf) ≫ (unitToHom j).val =
      PresheafOfModules.Monoidal.tensorHom j.val (𝟙 (dual M).val) ≫
        (schemeModuleTensorUnitLeftRawIso (dual M)).hom := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul m a =>
    change (unitToHom j).val.app W
        (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) W.unop m a) =
      j.val.app W m • a
    exact rankOneEvaluation_unitToHom_apply_of_pointwise_unitCharts j B hB eB W.unop m a

/-- The SAME GLOBAL sheafified evaluation/increment square. Its proof
uses the actual sheafification counit's naturality; no tensor-action
or sheafification comparison certificate is supplied. -/
theorem rankOneEvaluation_action_of_pointwise_unitCharts
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, M.over (B x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (B x)) :
    dualEvaluation M ≫ unitToHom j =
      schemeModuleTensorMap j (𝟙 (dual M)) ≫ (schemeModuleTensorUnitLeftIso (dual M)).hom := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let D := dual M
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let E := evaluationPresheaf M O
  let t := PresheafOfModules.Monoidal.tensorHom j.val (𝟙 D.val)
  let l := (schemeModuleTensorUnitLeftRawIso D).hom
  have hc : F.map (unitToHom j).val ≫ adj.counit.app D =
      adj.counit.app O ≫ unitToHom j := adj.counit.naturality (unitToHom j)
  have hraw : E ≫ (unitToHom j).val = t ≫ l :=
    rankOneEvaluation_presheaf_action_of_pointwise_unitCharts j B hB eB
  calc
    _ = (F.map E ≫ adj.counit.app O) ≫ unitToHom j :=
      congrArg (fun a => a ≫ unitToHom j) (evaluation_eq_sheafification_counit M O)
    _ = F.map E ≫ (F.map (unitToHom j).val ≫ adj.counit.app D) := by
      rw [Category.assoc, hc]
    _ = F.map (E ≫ (unitToHom j).val) ≫ adj.counit.app D := by
      rw [F.map_comp, Category.assoc]
    _ = F.map (t ≫ l) ≫ adj.counit.app D := congrArg (fun a => F.map a ≫ adj.counit.app D) hraw
    _ = F.map t ≫ (F.map l ≫ adj.counit.app D) := by rw [F.map_comp, Category.assoc]
    _ = _ := rfl

end PfaffianDescent.SchemeModuleInternalHom

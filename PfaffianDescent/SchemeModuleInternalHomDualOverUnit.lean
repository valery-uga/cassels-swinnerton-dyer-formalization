import PfaffianDescent.SchemeModuleInternalHomIncrementCoefficient

/-! Actual over-site unit chart of the CONSTRUCTED dual, derived from
the SAME original chart of M. Coefficients evaluate actual dual sections
on the actual restricted frame; naturality is derived from original
evaluation and the original chart inverse. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {M : X.Modules}

/-- The actual dual's coefficient morphism over U: evaluate a local
section on the SAME chart's actual frame at that smaller open. -/
def dualOverCoefficient (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (dual M).over U ⟶ (SheafOfModules.unit X.ringCatSheaf).over U where
  val :=
    { app := fun V => ModuleCat.ofHom
        (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V.unop.left
          (e.inv.val.app V (1 : Γ(X, V.unop.left))))
      naturality := by
        intro V W f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        have hgen : e.inv.val.app W (1 : Γ(X, W.unop.left)) =
            M.val.map f.unop.left.op (e.inv.val.app V (1 : Γ(X, V.unop.left))) := by
          have h := PresheafOfModules.naturality_apply e.inv.val f
            (1 : Γ(X, V.unop.left))
          have hone : ((SheafOfModules.unit X.ringCatSheaf).over U).val.map f
              (1 : Γ(X, V.unop.left)) = (1 : Γ(X, W.unop.left)) := by
            change X.presheaf.map f.unop.left.op 1 = 1
            exact map_one _
          rw [hone] at h
          exact h
        change evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) W.unop.left
            (e.inv.val.app W (1 : Γ(X, W.unop.left))) ((dual M).val.map f.unop.left.op a) =
          X.presheaf.map f.unop.left.op
            (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V.unop.left
              (e.inv.val.app V (1 : Γ(X, V.unop.left))) a)
        rw [hgen]
        exact (evaluationBilinear_restrict M (SheafOfModules.unit X.ringCatSheaf)
          f.unop.left (e.inv.val.app V (1 : Γ(X, V.unop.left))) a).symm }

/-- Restricting the actual chart yields its literal inverse frame. -/
theorem restrictedChart_frame (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) (V : Over U) :
    (overTopLinearEquiv M V.left (overUnitChartRestrict M V.hom e)).symm 1 =
      e.inv.val.app (op V) (1 : Γ(X, V.left)) := rfl

/-- The actual dual coefficient component is the same internally
constructed chart linear equivalence, so it is genuinely invertible. -/
theorem dualOverCoefficient_app_isIso (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (V : (Over U)ᵒᵖ) : IsIso ((dualOverCoefficient U e).val.app V) := by
  let eV := overUnitChartRestrict M V.unop.hom e
  have h : (dualOverCoefficient U e).val.app V =
      (dualCoefficientLinearEquiv V.unop.left eV).toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change a.1.app (op (Over.mk (𝟙 V.unop.left))) (e.inv.val.app V (1 : Γ(X, V.unop.left))) =
      a.1.app (op (Over.mk (𝟙 V.unop.left)))
        ((overTopLinearEquiv M V.unop.left eV).symm 1)
    rw [restrictedChart_frame]
  rw [h]
  infer_instance

/-- Genuine actual over-site unit Iso of the CONSTRUCTED dual. No dual
chart or fiber/invertibility certificate is supplied as an input. -/
def dualOverUnitIso (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (dual M).over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U := by
  haveI h (V : (Over U)ᵒᵖ) : IsIso ((dualOverCoefficient U e).val.app V) :=
    dualOverCoefficient_app_isIso U e V
  let eVal : ((dual M).over U).val ≅ ((SheafOfModules.unit X.ringCatSheaf).over U).val :=
    PresheafOfModules.isoMk (fun V => asIso ((dualOverCoefficient U e).val.app V))
      (fun {V W} f => (dualOverCoefficient U e).val.naturality f)
  exact (SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over U)).preimageIso eVal

/-- The unit Iso retains the SAME actual coefficient morphism. -/
theorem dualOverUnitIso_hom_val (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (dualOverUnitIso U e).hom.val = (dualOverCoefficient U e).val := by
  apply PresheafOfModules.hom_ext
  intro V
  rfl

end PfaffianDescent.SchemeModuleInternalHom

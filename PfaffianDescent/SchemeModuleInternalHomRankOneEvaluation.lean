import PfaffianDescent.SchemeModuleInternalHomEvaluation
import PfaffianDescent.CorayNormalizationClosedPointIdealAffineDual

/-! The CONSTRUCTED dual has the actual ring-linear dual sections on a
genuine rank-one over-site chart. The canonical RAW evaluation, without
replacement, is an isomorphism on that chart. The next module derives
GLOBAL sheafified IsIso using the actual chart basis and sheafification.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (M : X.Modules)

/-- Restriction of the actual structure module is the actual over-site
structure module. This compares ORIGINAL rings, not transported actions. -/
def unitOverIso (U : X.Opens) :
    (SheafOfModules.unit X.ringCatSheaf).over U ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) := Iso.refl _

/-- Actual top component of a genuine over-site rank-one chart. -/
def overTopLinearEquiv (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    M.val.obj (op U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  ((SheafOfModules.evaluation (X.ringCatSheaf.over U) (op (Over.mk (𝟙 U)))).mapIso e).toLinearEquiv

/-- The genuine local unit map supplies a section of the CONSTRUCTED
dual through the actual over-site Hom comparison. -/
def localUnitSection (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (dual M).val.obj (op U) :=
  (sectionsEquivOver M (SheafOfModules.unit X.ringCatSheaf) U).symm e.hom

/-- Every genuine dual section on the chart is its actual coefficient
times the actual unit-map section. Naturality at every smaller open and
local O-linearity prove this, rather than a prescribed section comparison. -/
theorem section_eq_coefficient_smul (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (a : (dual M).val.obj (op U)) :
    a = a.1.app (op (Over.mk (𝟙 U))) ((overTopLinearEquiv M U e).symm 1) •
      localUnitSection M U e := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  ext m
  let T : Over U := Over.mk (𝟙 U)
  let z : V.unop ⟶ T := Over.homMk V.unop.hom
  let b : M.val.obj (op U) := e.inv.val.app (op T) (1 : Γ(X, U))
  have hgen : e.inv.val.app V (1 : Γ(X, V.unop.left)) =
      M.val.map V.unop.hom.op b := by
    have h := PresheafOfModules.naturality_apply e.inv.val z.op (1 : Γ(X, U))
    have hone : ((SheafOfModules.unit X.ringCatSheaf).over U).val.map z.op
        (1 : Γ(X, U)) = (1 : Γ(X, V.unop.left)) := by
      change X.presheaf.map V.unop.hom.op 1 = 1
      exact map_one _
    rw [hone] at h
    exact h
  have hinv : e.inv.val.app V (e.hom.val.app V m) = m :=
    ConcreteCategory.congr_hom
      (congrArg (fun f : M.over U ⟶ M.over U => f.val.app V) e.hom_inv_id) m
  let c : Γ(X, V.unop.left) := e.hom.val.app V m
  have hcoord : c • e.inv.val.app V (1 : Γ(X, V.unop.left)) = m := by
    calc
      _ = e.inv.val.app V (c • (1 : Γ(X, V.unop.left))) :=
        ((e.inv.val.app V).hom.map_smul _ _).symm
      _ = e.inv.val.app V c := by rw [smul_eq_mul, mul_one]
      _ = m := hinv
  have hnat : a.1.app V (M.val.map V.unop.hom.op b) =
      X.presheaf.map V.unop.hom.op (a.1.app (op T) b) :=
    ConcreteCategory.congr_hom (a.1.naturality z.op) b
  change a.1.app V m =
    X.presheaf.map V.unop.hom.op (a.1.app (op T) b) * c
  calc
    a.1.app V m =
        a.1.app V (c • e.inv.val.app V (1 : Γ(X, V.unop.left))) :=
      congrArg (a.1.app V) hcoord.symm
    _ = c • (a.1.app V (e.inv.val.app V (1 : Γ(X, V.unop.left))) :
        Γ(X, V.unop.left)) := a.2 V.unop _ _
    _ = c • X.presheaf.map V.unop.hom.op (a.1.app (op T) b) := by
      rw [hgen, hnat]
    _ = _ := mul_comm _ _

/-- The ORIGINAL evaluation gives a linear map from actual dual-sheaf
sections to the actual ring-linear dual, even before choosing a chart. -/
def sectionToDual (U : X.Opens) :
    (dual M).val.obj (op U) →ₗ[Γ(X, U)] Module.Dual (Γ(X, U)) (M.val.obj (op U)) :=
  (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) U).flip

/-- Literal original evaluation value. -/
theorem sectionToDual_apply (U : X.Opens) (a : (dual M).val.obj (op U))
    (m : M.val.obj (op U)) :
    sectionToDual M U a m = a.1.app (op (Over.mk (𝟙 U))) m := rfl

/-- On a genuine rank-one chart, no linear functional is missing and
none of the actual dual sections is identified spuriously. -/
theorem sectionToDual_bijective (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    Function.Bijective (sectionToDual M U) := by
  let q := overTopLinearEquiv M U e
  let a₀ := localUnitSection M U e
  constructor
  · intro a b hab
    have h := congrArg (fun f : Module.Dual (Γ(X, U)) (M.val.obj (op U)) =>
      f (q.symm 1)) hab
    change a.1.app (op (Over.mk (𝟙 U))) (q.symm 1) =
      b.1.app (op (Over.mk (𝟙 U))) (q.symm 1) at h
    calc
      a = a.1.app (op (Over.mk (𝟙 U))) (q.symm 1) • a₀ :=
        section_eq_coefficient_smul M U e a
      _ = b.1.app (op (Over.mk (𝟙 U))) (q.symm 1) • a₀ := congrArg (· • a₀) h
      _ = b := (section_eq_coefficient_smul M U e b).symm
  · intro f
    refine ⟨f (q.symm 1) • a₀, ?_⟩
    apply LinearMap.ext
    intro m
    calc
      sectionToDual M U (f (q.symm 1) • a₀) m =
          f (q.symm 1) • sectionToDual M U a₀ m :=
        (evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) U m).map_smul _ _
      _ = f (q.symm 1) * q m := rfl
      _ = q m • f (q.symm 1) := mul_comm _ _
      _ = f (q m • q.symm 1) := (f.map_smul _ _).symm
      _ = f m := by
        rw [← q.symm.map_smul, smul_eq_mul, mul_one, q.symm_apply_apply]

/-- Genuine chart comparison of the CONSTRUCTED dual with the actual
ring-linear dual. Its scalar action was independently defined earlier. -/
def sectionDualLinearEquiv (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (dual M).val.obj (op U) ≃ₗ[Γ(X, U)] Module.Dual (Γ(X, U)) (M.val.obj (op U)) :=
  LinearEquiv.ofBijective (sectionToDual M U) (sectionToDual_bijective M U e)

/-- The RAW evaluation on a genuine chart is a linear equivalence with
the SAME literal evaluation map, using the prior canonical contractRight. -/
def rawEvaluationLinearEquiv (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    M.val.obj (op U) ⊗[Γ(X, U)] (dual M).val.obj (op U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  (TensorProduct.congr (LinearEquiv.refl (Γ(X, U)) (M.val.obj (op U)))
    (sectionDualLinearEquiv M U e)).trans
      (Coray.rankOneCanonicalDualTensorEquiv (overTopLinearEquiv M U e).symm)

/-- The chart equivalence is ACTUAL component evaluation. -/
theorem rawEvaluationLinearEquiv_apply (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (m : M.val.obj (op U)) (a : (dual M).val.obj (op U)) :
    rawEvaluationLinearEquiv M U e (m ⊗ₜ[Γ(X, U)] a) =
      a.1.app (op (Over.mk (𝟙 U))) m := rfl

/-- The actual raw tensor evaluation component is invertible on the
chart. This does NOT assert global sheafified evaluation IsIso. -/
theorem evaluationPresheaf_app_isIso (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    IsIso ((evaluationPresheaf M (SheafOfModules.unit X.ringCatSheaf)).app (op U)) := by
  let E := rawEvaluationLinearEquiv M U e
  have h : (evaluationPresheaf M (SheafOfModules.unit X.ringCatSheaf)).app (op U) =
      E.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m a
    rfl
  rw [h]
  infer_instance

end PfaffianDescent.SchemeModuleInternalHom

import PfaffianDescent.SchemeModuleInternalHomRankOneInverse
import PfaffianDescent.SchemeModuleInternalHomTensorCurry

/-! Arbitrary-target Hom coefficients on actual rank-one source charts.
All actions and over-site maps are native. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

private instance nativeSectionModule (A : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (A.val.obj (op U)) := (A.val.obj (op U)).isModule
private instance nativeOpSectionModule (A : X.Modules) (U : X.Opensᵒᵖ) :
    Module Γ(X, U.unop) (A.val.obj U) := (A.val.obj U).isModule
private instance nativeOverSectionModule (A : X.Modules) (U : X.Opens)
    (V : (Over U)ᵒᵖ) :
    Module Γ(X, V.unop.left) ((A.over U).val.obj V) :=
  ((A.over U).val.obj V).isModule

/-- An original N section gives its literal scalar-multiplication map
from the native structure module on every smaller open. -/
def unitSectionOver (U : X.Opens) (b : N.val.obj (op U)) :
    (SheafOfModules.unit X.ringCatSheaf).over U ⟶ N.over U where
  val :=
    { app := fun V => ModuleCat.ofHom (R := Γ(X, V.unop.left))
        (X := Γ(X, V.unop.left)) (Y := N.val.obj (op V.unop.left))
        { toFun := fun r => r •
            (show N.val.obj (op V.unop.left) from N.val.map V.unop.hom.op b)
          map_add' := fun r s => add_smul r s _
          map_smul' := by
            intro r s
            change (r * s) •
                (show N.val.obj (op V.unop.left) from N.val.map V.unop.hom.op b) =
              r • (s •
                (show N.val.obj (op V.unop.left) from N.val.map V.unop.hom.op b))
            exact mul_smul r s _ }
      naturality := by
        intro V W f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        have hb : N.val.map f.unop.left.op (N.val.map V.unop.hom.op b) =
            N.val.map W.unop.hom.op b := by
          rw [← N.val.map_comp_apply, ← op_comp, Over.w f.unop]
        let c : Γ(X, V.unop.left) := r
        let v : N.val.obj (op V.unop.left) := N.val.map V.unop.hom.op b
        let w : N.val.obj (op W.unop.left) := N.val.map W.unop.hom.op b
        change (show Γ(X, W.unop.left) from X.presheaf.map f.unop.left.op c) • w =
          N.val.map f.unop.left.op (c • v)
        exact (congrArg
          (fun n : N.val.obj (op W.unop.left) =>
            (show Γ(X, W.unop.left) from X.presheaf.map f.unop.left.op c) • n)
          hb).symm.trans (N.val.map_smul f.unop.left.op c v).symm }

/-- The actual Hom section obtained from a source chart and target section. -/
def homChartSection (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (b : N.val.obj (op U)) : (sheaf M N).val.obj (op U) :=
  (sectionsEquivOver M N U).symm (e.hom ≫ unitSectionOver N U b)

/-- Literal original component of the constructed Hom section. -/
theorem homChartSection_apply (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (b : N.val.obj (op U)) (V : Over U) (m : M.val.obj (op V.left)) :
    (homChartSection M N U e b).1.app (op V) m =
      (show Γ(X, V.left) from e.hom.val.app (op V) m) •
        (show N.val.obj (op V.left) from N.val.map V.hom.op b) := rfl

/-- Every actual Hom section is determined by its value on the genuine
source chart's frame, with coefficients in the ORIGINAL target module. -/
theorem homSection_chart_formula (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (a : (sheaf M N).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (m : M.val.obj (op V.unop.left)) :
    a.1.app V m = (show Γ(X, V.unop.left) from e.hom.val.app V m) •
      (show N.val.obj (op V.unop.left) from N.val.map V.unop.hom.op
        (((show M.val.obj (op U) →ₗ[Γ(X, U)]
          (sheaf M N).val.obj (op U) →ₗ[Γ(X, U)] N.val.obj (op U)
        from evaluationBilinear M N U).toFun
          ((overTopLinearEquiv M U e).symm.toFun (1 : Γ(X, U)))).toFun a)) := by
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
    exact (congrArg (e.inv.val.app V).hom hone).symm.trans h
  have hinv : e.inv.val.app V (e.hom.val.app V m) = m :=
    ConcreteCategory.congr_hom
      (congrArg (fun f : M.over U ⟶ M.over U => f.val.app V) e.hom_inv_id) m
  let c : Γ(X, V.unop.left) := e.hom.val.app V m
  have hcoord : c • e.inv.val.app V (1 : Γ(X, V.unop.left)) = m := by
    have hone : c • (1 : Γ(X, V.unop.left)) = c := mul_one c
    exact ((e.inv.val.app V).hom.map_smul c (1 : Γ(X, V.unop.left))).symm.trans
      ((congrArg (e.inv.val.app V).hom hone).trans hinv)
  have hnat : a.1.app V (M.val.map V.unop.hom.op b) =
      N.val.map V.unop.hom.op (a.1.app (op T) b) :=
    ConcreteCategory.congr_hom (a.1.naturality z.op) b
  change a.1.app V m = c •
    (show N.val.obj (op V.unop.left) from
      N.val.map V.unop.hom.op (a.1.app (op T) b))
  exact (congrArg (a.1.app V) hcoord.symm).trans
    ((a.2 V.unop c _).trans
      (congrArg (fun n : N.val.obj (op V.unop.left) => c • n)
        ((congrArg (a.1.app V) hgen).trans hnat)))

/-- Native chart coefficient map, using literal original evaluation. -/
def homChartCoefficient (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (sheaf M N).val.obj (op U) →ₗ[Γ(X, U)] N.val.obj (op U) :=
  (show M.val.obj (op U) →ₗ[Γ(X, U)]
          (sheaf M N).val.obj (op U) →ₗ[Γ(X, U)] N.val.obj (op U)
        from evaluationBilinear M N U).toFun
    ((overTopLinearEquiv M U e).symm.toFun (1 : Γ(X, U)))

/-- Actual source chart coefficients give a bijection with target sections. -/
theorem homChartCoefficient_bijective (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    Function.Bijective (homChartCoefficient M N U e) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    ext m
    exact (homSection_chart_formula M N U e a V m).trans
      ((congrArg (fun c : N.val.obj (op U) =>
        (show Γ(X, V.unop.left) from e.hom.val.app V m) •
        (show N.val.obj (op V.unop.left) from N.val.map V.unop.hom.op c)) hab).trans
        (homSection_chart_formula M N U e b V m).symm)
  · intro b
    refine ⟨homChartSection M N U e b, ?_⟩
    let T : Over U := Over.mk (𝟙 U)
    have hframe : e.hom.val.app (op T)
        (e.inv.val.app (op T) (1 : Γ(X, U))) = (1 : Γ(X, U)) :=
      ConcreteCategory.congr_hom
        (congrArg (fun f : (SheafOfModules.unit X.ringCatSheaf).over U ⟶
          (SheafOfModules.unit X.ringCatSheaf).over U => f.val.app (op T)) e.inv_hom_id) (1 : Γ(X, U))
    have hb : N.val.map (𝟙 U).op b = b := by
      change N.presheaf.map (𝟙 (op U)) b = b
      exact ConcreteCategory.congr_hom (N.presheaf.map_id (op U)) b
    change (show Γ(X, U) from e.hom.val.app (op T)
      (e.inv.val.app (op T) (1 : Γ(X, U)))) •
      (show N.val.obj (op U) from N.val.map (𝟙 U).op b) = b
    exact (congrArg (fun c : Γ(X, U) => c •
      (show N.val.obj (op U) from N.val.map (𝟙 U).op b)) hframe).trans
      ((one_smul (Γ(X, U))
        (show N.val.obj (op U) from N.val.map (𝟙 U).op b)).trans hb)

/-- Genuine linear equivalence of the actual Hom sections with N sections. -/
def homChartCoefficientLinearEquiv (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (sheaf M N).val.obj (op U) ≃ₗ[Γ(X, U)] N.val.obj (op U) :=
  LinearEquiv.ofBijective (homChartCoefficient M N U e)
    (homChartCoefficient_bijective M N U e)

/-- The canonical evaluation in actual chart coordinates. -/
theorem evaluationBilinear_chart_apply (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (m : M.val.obj (op U)) (a : (sheaf M N).val.obj (op U)) :
    ((show M.val.obj (op U) →ₗ[Γ(X, U)]
          (sheaf M N).val.obj (op U) →ₗ[Γ(X, U)] N.val.obj (op U)
        from evaluationBilinear M N U).toFun m).toFun a =
      (show M.val.obj (op U) ≃ₗ[Γ(X, U)] Γ(X, U)
        from overTopLinearEquiv M U e).toFun m • homChartCoefficient M N U e a := by
  have h := homSection_chart_formula M N U e a (op (Over.mk (𝟙 U))) m
  have hb : N.val.map (𝟙 U).op (homChartCoefficient M N U e a) =
      homChartCoefficient M N U e a := by
    change N.presheaf.map (𝟙 (op U)) _ = _
    exact ConcreteCategory.congr_hom (N.presheaf.map_id (op U)) _
  exact h.trans (congrArg (fun n : N.val.obj (op U) => (show M.val.obj (op U) ≃ₗ[Γ(X, U)] Γ(X, U)
        from overTopLinearEquiv M U e).toFun m • n) hb)

/-- The actual raw evaluation linear equivalence on a source chart. -/
def rawTargetEvaluationLinearEquiv (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    M.val.obj (op U) ⊗[Γ(X, U)] (sheaf M N).val.obj (op U) ≃ₗ[Γ(X, U)]
      N.val.obj (op U) :=
  (TensorProduct.congr
    (show M.val.obj (op U) ≃ₗ[Γ(X, U)] Γ(X, U)
      from overTopLinearEquiv M U e)
    (show (sheaf M N).val.obj (op U) ≃ₗ[Γ(X, U)] N.val.obj (op U)
      from homChartCoefficientLinearEquiv M N U e)).trans
      (TensorProduct.lid (Γ(X, U)) (N.val.obj (op U)))

/-- SAME raw evaluation, rather than an arbitrary selected linear map. -/
theorem rawTargetEvaluationLinearEquiv_apply (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (m : M.val.obj (op U)) (a : (sheaf M N).val.obj (op U)) :
    (show M.val.obj (op U) ⊗[Γ(X, U)] (sheaf M N).val.obj (op U) ≃ₗ[Γ(X, U)]
      N.val.obj (op U) from rawTargetEvaluationLinearEquiv M N U e).toFun
      (m ⊗ₜ[Γ(X, U)] a) =
      ((show M.val.obj (op U) →ₗ[Γ(X, U)]
          (sheaf M N).val.obj (op U) →ₗ[Γ(X, U)] N.val.obj (op U)
        from evaluationBilinear M N U).toFun m).toFun a := by
  exact (evaluationBilinear_chart_apply M N U e m a).symm

/-- The ORIGINAL raw evaluation component is invertible on a genuine chart. -/
theorem targetEvaluationPresheaf_app_isIso (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    IsIso ((evaluationPresheaf M N).app (op U)) := by
  let E : M.val.obj (op U) ⊗[Γ(X, U)] (sheaf M N).val.obj (op U) ≃ₗ[Γ(X, U)]
      N.val.obj (op U) := rawTargetEvaluationLinearEquiv M N U e
  have h : (evaluationPresheaf M N).app (op U) = E.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m a
    exact (rawTargetEvaluationLinearEquiv_apply M N U e m a).symm
  exact h.symm ▸ E.toModuleIso.isIso_hom

end PfaffianDescent.SchemeModuleInternalHom
end

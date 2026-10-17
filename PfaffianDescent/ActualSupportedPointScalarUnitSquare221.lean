import PfaffianDescent.ActualSupportedPointSourceCoordinate213
import PfaffianDescent.CubicPointTraceFieldBaseChangePointSummand
import PfaffianDescent.FieldPointExtCoordinate

/-! SOURCE ONLY221. The actual point scalar family and the actual unit
restriction commute through the SAME whole supported-source coordinate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal supported-point scalar restriction equals the pushforward
of the original scalar section of the SAME whole quotient. No unit/source
square, comparison, or nonzero assertion is supplied by the caller. -/
theorem actualSupportedPointWholeSource_scalarUnitSquare221
    {X Y : Scheme.{u}} (s : X ⟶ Y) [IsClosedImmersion s]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (Q : X.Modules)
    (E : Q ≅ (Scheme.Modules.pushforward i).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (a : L) :
    let G := Scheme.Modules.pushforward s
    let c := closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)
    let beta := actualSupportedPointWholeSourceIso213 s i Q E
    let gamma := closedImmersionUnitToPushforwardUnit (i ≫ s) ≫ c.inv
    let sigma := c.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom (i ≫ s) a ≫ c.inv
    let aQ := closedImmersionUnitToPushforwardUnit i ≫
      fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv
    gamma ≫ sigma ≫ beta.hom = closedImmersionUnitToPushforwardUnit s ≫ G.map aQ := by
  dsimp only
  let G := Scheme.Modules.pushforward s
  let U : (Spec (.of L)).Modules := SheafOfModules.unit (Spec (.of L)).ringCatSheaf
  let C := (Scheme.Modules.pushforwardComp i s).app U
  let c := closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ s)
  let scalar := schemeModuleConstantEndomorphism (𝟙 (Spec (.of L))) a
  have hNat : fieldPointPushforwardScalarEndomorphismAddHom (i ≫ s) a ≫ C.inv =
      C.inv ≫ G.map (fieldPointPushforwardScalarEndomorphismAddHom i a) := by
    exact ((Scheme.Modules.pushforwardComp i s).inv.naturality scalar)
  have hUnit : closedImmersionUnitToPushforwardUnit (i ≫ s) ≫ C.inv =
      closedImmersionUnitToPushforwardUnit s ≫ G.map (closedImmersionUnitToPushforwardUnit i) := by
    have hComp : closedImmersionUnitToPushforwardUnit s ≫
        G.map (closedImmersionUnitToPushforwardUnit i) ≫ C.hom =
        closedImmersionUnitToPushforwardUnit (i ≫ s) :=
      cubicPointTraceFieldBaseChange_unitPushforward_comp i s
    apply (cancel_mono C.hom).mp
    calc
      (closedImmersionUnitToPushforwardUnit (i ≫ s) ≫ C.inv) ≫ C.hom =
          closedImmersionUnitToPushforwardUnit (i ≫ s) := by
        rw [Category.assoc, C.inv_hom_id, Category.comp_id]
      _ = (closedImmersionUnitToPushforwardUnit s ≫
          G.map (closedImmersionUnitToPushforwardUnit i)) ≫ C.hom := by
        simpa only [Category.assoc] using hComp.symm
  have hBeta : (actualSupportedPointWholeSourceIso213 s i Q E).hom =
      c.hom ≫ C.inv ≫ G.map E.inv := rfl
  calc
    (closedImmersionUnitToPushforwardUnit (i ≫ s) ≫ c.inv) ≫
        (c.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom (i ≫ s) a ≫ c.inv) ≫
        (actualSupportedPointWholeSourceIso213 s i Q E).hom =
      closedImmersionUnitToPushforwardUnit (i ≫ s) ≫
        (fieldPointPushforwardScalarEndomorphismAddHom (i ≫ s) a ≫ C.inv) ≫ G.map E.inv := by
          rw [hBeta]
          simp only [Category.assoc, c.inv_hom_id_assoc]
    _ = closedImmersionUnitToPushforwardUnit (i ≫ s) ≫
        (C.inv ≫ G.map (fieldPointPushforwardScalarEndomorphismAddHom i a)) ≫ G.map E.inv :=
      congrArg (fun v => closedImmersionUnitToPushforwardUnit (i ≫ s) ≫ v ≫ G.map E.inv) hNat
    _ = (closedImmersionUnitToPushforwardUnit s ≫
        G.map (closedImmersionUnitToPushforwardUnit i)) ≫
          G.map (fieldPointPushforwardScalarEndomorphismAddHom i a) ≫ G.map E.inv := by
      simpa only [Category.assoc] using congrArg (fun v => v ≫
        G.map (fieldPointPushforwardScalarEndomorphismAddHom i a) ≫ G.map E.inv) hUnit
    _ = _ := by
      change (closedImmersionUnitToPushforwardUnit s ≫
        G.map (closedImmersionUnitToPushforwardUnit i)) ≫
          G.map (fieldPointPushforwardScalarEndomorphismAddHom i a) ≫ G.map E.inv =
        closedImmersionUnitToPushforwardUnit s ≫ G.map
          (closedImmersionUnitToPushforwardUnit i ≫
            fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv)
      simp only [Functor.map_comp, Category.assoc]

/-- Rewriting the literal unit-twist point target through its canonical iso
preserves the entire scalar-precomposition family. This is the exact source
coordinate needed by the existing finite-separable diagonal zero descent. -/
theorem actualSupportedPointUnitTarget_scalarPrecomp221
    {Y : Scheme.{u}} [CategoryTheory.HasExt.{u} Y.Modules]
    {L : Type u} [Field L] (j : Spec (.of L) ⟶ Y) [IsClosedImmersion j]
    (N : Y.Modules)
    (z : CategoryTheory.Abelian.Ext.{u} (C := Y.Modules)
      (closedImmersionIdealTwistSequence j
        (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)).X₃ N 2) (a : L) :
    let c := closedImmersionIdealTwistSequenceUnitTargetIso j
    let gamma := closedImmersionUnitToPushforwardUnit j ≫ c.inv
    let sigma := c.hom ≫ fieldPointPushforwardScalarEndomorphismAddHom j a ≫ c.inv
    (CategoryTheory.Abelian.Ext.mk₀.{u} (C := Y.Modules) gamma).comp
      ((CategoryTheory.Abelian.Ext.mk₀.{u} (C := Y.Modules) sigma).comp z (zero_add 2))
      (zero_add 2) =
    (CategoryTheory.Abelian.Ext.mk₀.{u} (C := Y.Modules)
      (closedImmersionUnitToPushforwardUnit j)).comp
      ((CategoryTheory.Abelian.Ext.mk₀.{u} (C := Y.Modules)
        (fieldPointPushforwardScalarEndomorphismAddHom j a)).comp
        ((CategoryTheory.Abelian.Ext.mk₀.{u} (C := Y.Modules) c.inv).comp z (zero_add 2))
        (zero_add 2)) (zero_add 2) := by
  dsimp only
  simp only [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc,
    Category.assoc, Iso.inv_hom_id_assoc]

end PfaffianDescent

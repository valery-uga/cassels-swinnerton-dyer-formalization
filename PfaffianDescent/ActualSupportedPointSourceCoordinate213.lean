import PfaffianDescent.OriginalCurveSurfaceSupportedCoordinates210
import PfaffianDescent.PointCartierNativeStalkPushforwardComparison
import PfaffianDescent.ActualOriginalResiduePointFiberStalkCoordinate207

/-! SOURCE ONLY213. The literal supported SOURCE in210, its actual
pushforward-stalk comparison, and its canonical original point value. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SchemeModuleInternalHom IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- This is the literal210 source Iso for an arbitrary actual curve immersion.
For f=e.hom≫cubicSecondEquationCurveImmersion it is definitionally210.beta. -/
def actualSupportedPointWholeSourceIso213
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (Q : X.Modules)
    (E : Q ≅ (Scheme.Modules.pushforward i).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) :
    (closedImmersionIdealTwistSequence (i ≫ f)
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)).X₃ ≅
      (Scheme.Modules.pushforward f).obj Q :=
  closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ f) ≪≫
    ((Scheme.Modules.pushforwardComp i f).app
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso E.symm

/-- The actual source-coordinate square, proved by native stalk naturality.
The original whole E cancels; no source/augmentation comparison is supplied. -/
theorem actualSupportedPointWholeSource_nativeSquare213
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : X) (Q : X.Modules)
    (E : Q ≅ (Scheme.Modules.pushforward i).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) :
    let H := schemeModuleStalkModuleFunctor Y (f x)
    let F := schemeModuleStalkModuleFunctor X x
    let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
    let P := (Scheme.Modules.pushforward i).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    let etaQ := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x Q
    let etaP := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x P
    (H.map (actualSupportedPointWholeSourceIso213 f i Q E).hom ≫ etaQ.hom) ≫
        Phi.map (F.map E.hom) =
      H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ f)).hom ≫
        H.map ((Scheme.Modules.pushforwardComp i f).app
          (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).inv ≫
          etaP.hom := by
  dsimp only
  let H := schemeModuleStalkModuleFunctor Y (f x)
  let F := schemeModuleStalkModuleFunctor X x
  let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
  let P := (Scheme.Modules.pushforward i).obj
    (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  let etaQ := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x Q
  let etaP := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x P
  have hNat : H.map ((Scheme.Modules.pushforward f).map E.inv) ≫ etaQ.hom =
      etaP.hom ≫ Phi.map (F.map E.inv) := by
    exact (pointCartierNativeStalkPushforwardNatIso f f.isClosedEmbedding.isInducing x).hom.naturality E.inv
  have hCancel : (H.map ((Scheme.Modules.pushforward f).map E.inv) ≫ etaQ.hom) ≫
      Phi.map (F.map E.hom) = etaP.hom := by
    rw [hNat, Category.assoc, ← Phi.map_comp, ← F.map_comp,
      E.inv_hom_id, F.map_id, Phi.map_id, Category.comp_id]
  let c := closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ f)
  let v := (Scheme.Modules.pushforwardComp i f).app
    (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  have hMap : H.map (actualSupportedPointWholeSourceIso213 f i Q E).hom =
      H.map c.hom ≫ H.map v.inv ≫ H.map ((Scheme.Modules.pushforward f).map E.inv) := by
    change H.map (c.hom ≫ v.inv ≫ (Scheme.Modules.pushforward f).map E.inv) = _
    exact (H.map_comp c.hom (v.inv ≫ (Scheme.Modules.pushforward f).map E.inv)).trans
      (congrArg (fun z => H.map c.hom ≫ z)
        (H.map_comp v.inv ((Scheme.Modules.pushforward f).map E.inv)))
  calc
    _ = ((H.map c.hom ≫ H.map v.inv ≫
        H.map ((Scheme.Modules.pushforward f).map E.inv)) ≫ etaQ.hom) ≫
          Phi.map (F.map E.hom) :=
      congrArg (fun z => (z ≫ etaQ.hom) ≫ Phi.map (F.map E.hom)) hMap
    _ = H.map c.hom ≫ H.map v.inv ≫
        ((H.map ((Scheme.Modules.pushforward f).map E.inv) ≫ etaQ.hom) ≫
          Phi.map (F.map E.hom)) := by simp only [Category.assoc]
    _ = H.map c.hom ≫ H.map v.inv ≫ etaP.hom :=
      congrArg (fun z => H.map c.hom ≫ H.map v.inv ≫ z) hCancel

private theorem actualPushforwardUnit_comp213
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ Y) :
    closedImmersionUnitToPushforwardUnit (i ≫ f) ≫
        ((Scheme.Modules.pushforwardComp i f).app
          (show Z.Modules from SheafOfModules.unit Z.ringCatSheaf)).inv =
      closedImmersionUnitToPushforwardUnit f ≫
        (Scheme.Modules.pushforward f).map (closedImmersionUnitToPushforwardUnit i) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (i ≫ f).app U.unop r = i.app (f ⁻¹ᵁ U.unop) (f.app U.unop r)
  rfl

/-- The SAME actual surface supported-source map sends canonical restriction
of r to the original point residue of the literal original stalk map f(r).
This preserves the actual surface point target and its canonical projection. -/
theorem actualSupportedPointWholeSource_ringCoordinate213
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (y : Spec (.of L)) (Q : X.Modules)
    (E : Q ≅ (Scheme.Modules.pushforward i).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (r : Y.presheaf.stalk (f (i y))) :
    let H := schemeModuleStalkModuleFunctor Y (f (i y))
    let F := schemeModuleStalkModuleFunctor X (i y)
    let beta := actualSupportedPointWholeSourceIso213 f i Q E
    let etaQ := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing (i y) Q
    let z := (H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ f)).inv)
      (closedImmersionPushforwardStalkFromRingLinearMap (i ≫ f) (f (i y)) r)
    actualFieldPointPushforwardUnitStalkCoordinate207 i y
        ((F.map E.hom) ((H.map beta.hom ≫ etaQ.hom) z)) =
      closedFieldPointResidueRingEquivAt i y (X.residue (i y) (f.stalkMap (i y) r)) := by
  dsimp only
  let H := schemeModuleStalkModuleFunctor Y (f (i y))
  let F := schemeModuleStalkModuleFunctor X (i y)
  let P := (Scheme.Modules.pushforward i).obj
    (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
  let etaP := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing (i y) P
  let etaO := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing (i y)
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let z := (H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ f)).inv)
    (closedImmersionPushforwardStalkFromRingLinearMap (i ≫ f) (f (i y)) r)
  have hSquare := ConcreteCategory.congr_hom
    (actualSupportedPointWholeSource_nativeSquare213 f i (i y) Q E) z
  have hComp := congrArg H.map (actualPushforwardUnit_comp213 i f)
  rw [H.map_comp, H.map_comp] at hComp
  have hValue := ConcreteCategory.congr_hom hComp
    ((schemeModuleUnitStalkIso Y (f (i y))).inv r)
  change (H.map ((Scheme.Modules.pushforwardComp i f).app
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).inv)
        (closedImmersionPushforwardStalkFromRingLinearMap (i ≫ f) (f (i y)) r) =
    (H.map ((Scheme.Modules.pushforward f).map (closedImmersionUnitToPushforwardUnit i)))
      (closedImmersionPushforwardStalkFromRingLinearMap f (f (i y)) r) at hValue
  have hNat := ConcreteCategory.congr_hom
    ((pointCartierNativeStalkPushforwardNatIso f f.isClosedEmbedding.isInducing (i y)).hom.naturality
      (closedImmersionUnitToPushforwardUnit i))
    (closedImmersionPushforwardStalkFromRingLinearMap f (f (i y)) r)
  have hRing := closedImmersionPushforwardStalkFromRingLinearMap_comp_stalkPushforward f (i y) r
  have hActual : ((F.map E.hom)
      ((H.map (actualSupportedPointWholeSourceIso213 f i Q E).hom ≫
        (pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing (i y) Q).hom) z)) =
      closedImmersionPushforwardStalkFromRingLinearMap i (i y) (f.stalkMap (i y) r) := by
    have hCancel : (H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ f)).hom) z =
        closedImmersionPushforwardStalkFromRingLinearMap (i ≫ f) (f (i y)) r := by
      have h := ConcreteCategory.congr_hom
        (H.mapIso (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ f))).inv_hom_id
        (closedImmersionPushforwardStalkFromRingLinearMap (i ≫ f) (f (i y)) r)
      change (H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ f)).hom) z =
        (𝟙 (H.obj ((Scheme.Modules.pushforward (i ≫ f)).obj
          (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))))
            (closedImmersionPushforwardStalkFromRingLinearMap (i ≫ f) (f (i y)) r) at h
      exact h.trans (ModuleCat.id_apply _ _)
    have hSquare' := hSquare
    change ((F.map E.hom)
      ((H.map (actualSupportedPointWholeSourceIso213 f i Q E).hom ≫
        (pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing (i y) Q).hom) z)) =
      etaP.hom ((H.map ((Scheme.Modules.pushforwardComp i f).app
        (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).inv)
          ((H.map (closedImmersionIdealTwistSequenceUnitTargetIso (i ≫ f)).hom) z)) at hSquare'
    have hCancelStep := congrArg (fun w => etaP.hom
      ((H.map ((Scheme.Modules.pushforwardComp i f).app
        (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).inv) w))
      hCancel
    have hValueStep := congrArg (fun w => etaP.hom w) hValue
    have hSquareValue := hSquare'.trans (hCancelStep.trans hValueStep)
    change etaP.hom
        ((H.map ((Scheme.Modules.pushforward f).map (closedImmersionUnitToPushforwardUnit i)))
          (closedImmersionPushforwardStalkFromRingLinearMap f (f (i y)) r)) =
      (F.map (closedImmersionUnitToPushforwardUnit i))
        (etaO.hom (closedImmersionPushforwardStalkFromRingLinearMap f (f (i y)) r)) at hNat
    have hUnit : etaO.hom (closedImmersionPushforwardStalkFromRingLinearMap f (f (i y)) r) =
        (schemeModuleUnitStalkIso X (i y)).inv (f.stalkMap (i y) r) := by
      have hUnitValue : (schemeModuleUnitStalkIso X (i y)).hom
          (etaO.hom (closedImmersionPushforwardStalkFromRingLinearMap f (f (i y)) r)) =
          f.stalkMap (i y) r := hRing
      apply (ConcreteCategory.bijective_of_isIso
        (schemeModuleUnitStalkIso X (i y)).hom).injective
      exact hUnitValue.trans (ConcreteCategory.congr_hom
        (schemeModuleUnitStalkIso X (i y)).inv_hom_id (f.stalkMap (i y) r)).symm
    have hUnitStep := congrArg (fun w => (F.map (closedImmersionUnitToPushforwardUnit i)) w) hUnit
    exact hSquareValue.trans (hNat.trans hUnitStep)
  have hCoordinate := congrArg (actualFieldPointPushforwardUnitStalkCoordinate207 i y) hActual
  exact hCoordinate.trans
    ((actualFieldPointPushforwardUnitStalkCoordinate_fromRing207 i y (f.stalkMap (i y) r)).trans
      (closedFieldPointResidueRingEquivAt_residue_eq_stalkMap i y _).symm)

end PfaffianDescent

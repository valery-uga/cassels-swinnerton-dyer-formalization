import PfaffianDescent.SchemeModuleFiberFrameCoherence
import PfaffianDescent.SchemeModuleActualOverNativeStalkChart191
import PfaffianDescent.SchemeModuleInternalHomRestrictedFiberIso
import PfaffianDescent.ActualOriginalPointIdealDualStalkComparison191

/-! SOURCE ONLY207. Literal actual fiber-unit maps factor on native stalks
through the actual original chart. Both restriction squares are already
proved; cancellation derives the map equality rather than assuming it. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeModuleInternalHom IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME actual adjunction unit in the actual point fiber chart. -/
def actualPointChartFiberUnitMap207
    {X Y : Scheme.{u}} (U : X.Opens) (j : Y ⟶ (U : Scheme)) (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      (show (U : Scheme).Modules from SheafOfModules.unit (U : Scheme).ringCatSheaf)) :
    T ⟶ (Scheme.Modules.pushforward (j ≫ U.ι)).obj
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app T ≫
    (Scheme.Modules.pushforward (j ≫ U.ι)).map
      (schemeModuleFiberFrameIso U.ι j T eT).hom

/-- Cancel the SAME genuine point/open support Iso in the actual fiber
and unit restriction squares. No chart/fiber comparison is a premise. -/
theorem actualPointChartFiberUnitMap_restrict_factor207
    {X Y : Scheme.{u}} (U : X.Opens) (j : Y ⟶ (U : Scheme)) (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      (show (U : Scheme).Modules from SheafOfModules.unit (U : Scheme).ringCatSheaf)) :
    (Scheme.Modules.restrictFunctor U.ι).map (actualPointChartFiberUnitMap207 U j T eT) =
      (eT ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm).hom ≫
        (Scheme.Modules.restrictFunctor U.ι).map
          (closedImmersionUnitToPushforwardUnit (j ≫ U.ι)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let k := restrictPushforwardUnitFactorThroughOpenIso j U.ι
  let v := Scheme.Modules.restrictUnitIso U.ι
  let q := closedImmersionUnitToPushforwardUnit (j ≫ U.ι)
  apply (cancel_mono k.hom).mp
  change R.map (actualPointChartFiberUnitMap207 U j T eT) ≫ k.hom =
    (eT.hom ≫ v.inv ≫ R.map q) ≫ k.hom
  calc
    _ = eT.hom ≫ closedImmersionUnitToPushforwardUnit j := by
      dsimp only [actualPointChartFiberUnitMap207]
      rw [R.map_comp]
      exact schemeModuleFiberFrameIso_restrict_unit_square U.ι j T eT
    _ = _ := by
      rw [Category.assoc, Category.assoc,
        cubicClosedPointSerreSurfaceJetCotangent_closedQuotient_openRestriction]
      change eT.hom ≫ closedImmersionUnitToPushforwardUnit j =
        eT.hom ≫ v.inv ≫ v.hom ≫ closedImmersionUnitToPushforwardUnit j
      exact (congrArg (fun w => eT.hom ≫ w)
        (Iso.inv_hom_id_assoc v (closedImmersionUnitToPushforwardUnit j))).symm

/-- The actual restriction factor is carried to SAME original native
stalks using existing191 local composition/restriction, without a new
pullback-stalk comparison object. -/
theorem actualPointChartFiberUnitMap_native_factor207
    {X Y : Scheme.{u}} (U : X.Opens) (j : Y ⟶ (U : Scheme)) (y : Y) (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      (show (U : Scheme).Modules from SheafOfModules.unit (U : Scheme).ringCatSheaf)) :
    (schemeModuleStalkModuleFunctor X (U.ι (j y))).map
        (actualPointChartFiberUnitMap207 U j T eT) =
      (schemeModuleLocalStalkModuleIso U (j y) T
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
        (eT ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm)).hom ≫
      (schemeModuleStalkModuleFunctor X (U.ι (j y))).map
        (closedImmersionUnitToPushforwardUnit (j ≫ U.ι)) := by
  let N := (Scheme.Modules.pushforward (j ≫ U.ι)).obj
    (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let p := (eT ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm).hom
  let q := closedImmersionUnitToPushforwardUnit (j ≫ U.ι)
  calc
    _ = cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U (j y) T N
        ((Scheme.Modules.restrictFunctor U.ι).map
          (actualPointChartFiberUnitMap207 U j T eT)) :=
      (cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_restrict
        U (j y) T N (actualPointChartFiberUnitMap207 U j T eT)).symm
    _ = cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U (j y) T N
        (p ≫ (Scheme.Modules.restrictFunctor U.ι).map q) := by
      rw [actualPointChartFiberUnitMap_restrict_factor207 U j T eT]
    _ = cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U (j y) T O p ≫
        cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U (j y) O N
          ((Scheme.Modules.restrictFunctor U.ι).map q) :=
      cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_comp U (j y) T O N p _
    _ = _ := by
      rw [← actualLocalStalkModuleIso_hom191,
        cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_restrict]

/-- The actual dual restriction/unit coordinate agrees with the existing191
native actual dual chart. Only the genuine unit-Iso cancellation is used. -/
theorem actualDualChartLocalUnitStalkIso_eq207
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    schemeModuleLocalUnitStalkIso U x (dual M) (dualRestrictUnitIso U e) =
      actualDualFrameNativeStalkIso191 U x M e := by
  have h : dualRestrictUnitIso U e ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm =
      actualOverRestrictedChartIso191 U (dualOverUnitIso U e) := by
    dsimp only [dualRestrictUnitIso, actualOverRestrictedChartIso191]
    simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  dsimp only [schemeModuleLocalUnitStalkIso, actualDualFrameNativeStalkIso191,
    actualOverNativeStalkChartIso191]
  rw [h]

/-- Exact SAME native dual chart factor. The literal original canonical
point map is retained; neither a fiber nor residue comparison is assumed. -/
theorem actualDualChartFiberUnitMap_native_factor207
    {X Y : Scheme.{u}} (U : X.Opens) (j : Y ⟶ (U : Scheme)) (y : Y) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (schemeModuleStalkModuleFunctor X (U.ι (j y))).map
        (actualPointChartFiberUnitMap207 U j (dual M) (dualRestrictUnitIso U e)) =
      (actualDualFrameNativeStalkIso191 U (j y) M e).hom ≫
        (schemeModuleUnitStalkIso X (U.ι (j y))).inv ≫
          (schemeModuleStalkModuleFunctor X (U.ι (j y))).map
            (closedImmersionUnitToPushforwardUnit (j ≫ U.ι)) := by
  have h := actualPointChartFiberUnitMap_native_factor207 U j y (dual M)
    (dualRestrictUnitIso U e)
  have he := congrArg (fun a => a.hom)
    (actualDualChartLocalUnitStalkIso_eq207 U (j y) M e)
  change (schemeModuleLocalStalkModuleIso U (j y) (dual M)
      (SheafOfModules.unit X.ringCatSheaf)
      (dualRestrictUnitIso U e ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm)).hom ≫
        (schemeModuleUnitStalkIso X (U.ι (j y))).hom =
          (actualDualFrameNativeStalkIso191 U (j y) M e).hom at he
  have hp := (Iso.eq_comp_inv (schemeModuleUnitStalkIso X (U.ι (j y)))).mpr he
  rw [hp] at h
  simpa only [Category.assoc] using h

end PfaffianDescent

import PfaffianDescent.SchemeModuleFiberFrameCoherence
import PfaffianDescent.SchemeModuleInternalHomCanonicalFiberMap
import PfaffianDescent.SchemeModuleInternalHomIncrementChartCokernel

/-! The SAME actual canonical cokernel-to-intrinsic-fiber map is
invertible after restriction to a unit chart containing the closed
immersion. Actual cokernel projections and actual adjunction-unit
squares prove the comparison; no desired-map certificate is input.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {M : X.Modules}

/-- Restriction of the CONSTRUCTED dual is the unit on an actual chart
of M, through the actual over-site equivalence and original unit Iso. -/
def dualRestrictUnitIso (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (Scheme.Modules.restrictFunctor U.ι).obj (dual M) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv U).app (dual M)).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso (dualOverUnitIso U e) ≪≫
    (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    Scheme.Modules.restrictUnitIso U.ι

/-- Actual GLOBAL cokernel restricted to the chart, with the genuine
chosen-chart comparison from its original global cokernel cofork. -/
def closedImmersionDualIncrement_restrictCokernelIso
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (e : (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U) :
    (Scheme.Modules.restrictFunctor U.ι).obj
        (cokernel (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit (j ≫ U.ι)))) ≅
      (Scheme.Modules.pushforward j).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  ((Scheme.Modules.overFunctorEquiv U).app _).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso
      (closedImmersionIncrement_cokernelOverIso (j ≫ U.ι) B hB eB U e) ≪≫
    (Scheme.Modules.overFunctorEquiv U).app _ ≪≫
    restrictPushforwardUnitFactorThroughOpenIso j U.ι

/-- The actual restricted GLOBAL projection is the literal closed-chart
quotient in the SAME dual frame. No sections/cokernel interchange is
assumed, and no map square is supplied as an input. -/
theorem closedImmersionDualIncrement_restrictCokernelIso_projection
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (e : (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U) :
    (Scheme.Modules.restrictFunctor U.ι).map
        (cokernel.π (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit (j ≫ U.ι)))) ≫
      (closedImmersionDualIncrement_restrictCokernelIso U j B hB eB e).hom =
    (dualRestrictUnitIso U e).hom ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j := by
  let i := j ≫ U.ι
  let D := dual (IdealSheafDataModule.closedImmersionModule i)
  let C := cokernel (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i))
  let O := SheafOfModules.unit X.ringCatSheaf
  let A := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let R := Scheme.Modules.restrictFunctor U.ι
  let E := (Scheme.Modules.overEquiv U).functor
  let n := Scheme.Modules.overFunctorEquiv U
  let pi := cokernel.π (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i))
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let c := closedImmersionIncrement_cokernelOverIso i B hB eB U e
  let d := dualOverUnitIso U e
  let k := restrictPushforwardUnitFactorThroughOpenIso j U.ι
  have hpi := n.inv.naturality pi
  change R.map pi ≫ (n.app C).inv = (n.app D).inv ≫ E.map (pi.over U) at hpi
  have hq := n.hom.naturality q
  change E.map (q.over U) ≫ (n.app A).hom = (n.app O).hom ≫ R.map q at hq
  have hc := congrArg E.map
    (closedImmersionIncrement_cokernelOverIso_projection i B hB eB U e)
  change E.map (pi.over U ≫ c.hom) = E.map (d.hom ≫ q.over U) at hc
  have hcomp : E.map (pi.over U) ≫ E.map c.hom =
      E.map d.hom ≫ E.map (q.over U) := by
    rw [← E.map_comp, ← E.map_comp]
    exact hc
  change R.map pi ≫ ((n.app C).inv ≫ E.map c.hom ≫ (n.app A).hom ≫ k.hom) =
    ((n.app D).inv ≫ E.map d.hom ≫ (n.app O).hom ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j
  rw [← Category.assoc, hpi]
  simp only [Category.assoc]
  rw [← Category.assoc (E.map (pi.over U)), hcomp]
  simp only [Category.assoc]
  rw [← Category.assoc (E.map (q.over U)), hq]
  simp only [Category.assoc]
  rw [cubicClosedPointSerreSurfaceJetCotangent_closedQuotient_openRestriction]

/-- Invertibility of the SAME canonical fiber map after actual open
restriction. Both comparison squares and the epimorphic original
projection are internally proved from actual exact sequences. -/
theorem closedImmersionDualIncrement_restrictFiberMap_isIso
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (e : (IdealSheafDataModule.closedImmersionModule (j ≫ U.ι)).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (closedImmersionDualIncrement_fiberMap (j ≫ U.ι) B hB eB)) := by
  let i := j ≫ U.ι
  let M := IdealSheafDataModule.closedImmersionModule i
  let D := dual M
  let R := Scheme.Modules.restrictFunctor U.ι
  let pi := cokernel.π (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i))
  let a := closedImmersionDualIncrement_fiberMap i B hB eB
  let S := incrementCokernelSequence (IdealSheafDataModule.closedImmersionModuleToUnit i)
  letI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  have hS := incrementCokernelSequence_shortExact_of_pointwise_unitCharts
    (IdealSheafDataModule.closedImmersionModuleToUnit i) B hB eB
  have hSR := ShortComplex.shortExact_map_restrictFunctor U.ι S hS
  haveI : Epi (R.map pi) := by
    change Epi (S.map R).g
    exact hSR.epi_g
  let eD := dualRestrictUnitIso U e
  let eC := closedImmersionDualIncrement_restrictCokernelIso U j B hB eB e
  let eF := R.mapIso ((Scheme.Modules.pushforward i).mapIso
      (schemeModuleFiberFrameIso U.ι j D eD)) ≪≫
    restrictPushforwardUnitFactorThroughOpenIso j U.ι
  have hpi : R.map pi ≫ R.map a =
      R.map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D) := by
    rw [← R.map_comp, closedImmersionDualIncrement_fiberMap_projection]
  have hframe : R.map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D) ≫
      eF.hom = eD.hom ≫ IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j :=
    schemeModuleFiberFrameIso_restrict_unit_square U.ι j D eD
  have hC := closedImmersionDualIncrement_restrictCokernelIso_projection U j B hB eB e
  have heq : R.map a ≫ eF.hom = eC.hom := by
    apply (cancel_epi (R.map pi)).mp
    calc
      R.map pi ≫ (R.map a ≫ eF.hom) =
          R.map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D) ≫ eF.hom := by
        rw [← Category.assoc, hpi]
      _ = eD.hom ≫ IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j := hframe
      _ = R.map pi ≫ eC.hom := hC.symm
  haveI : IsIso (R.map a ≫ eF.hom) := by rw [heq]; infer_instance
  exact IsIso.of_isIso_comp_right (R.map a) eF.hom

end PfaffianDescent.SchemeModuleInternalHom

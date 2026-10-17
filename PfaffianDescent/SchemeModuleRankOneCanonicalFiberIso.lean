import PfaffianDescent.SchemeModuleLocallyRankOneTensor
import PfaffianDescent.SchemeModuleFiberFrameCoherence
import PfaffianDescent.SchemeModuleCanonicalFiberProjection
import PfaffianDescent.FiniteProjectiveProjectionFormula
import PfaffianDescent.SchemeModuleCoverEqualizer

/-! Invertibility of the SAME canonical tensor-to-intrinsic-fiber morphism
for an actual rank-one coefficient whose closed support lies in a unit chart.
The local fiber square and epimorphic quotient derive the map identification.
No desired projection-formula, exactness or dimension certificate is input.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- Local invertibility of the SAME canonical fiber projection. The chosen
fiber frame is defined from the actual tensor restriction component at O;
this makes the original unit/quotient square a formal naturality identity. -/
theorem schemeModuleCanonicalFiberProjection_restrict_isIso_of_unitCharts
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)] (T : X.Modules)
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, T.over (B x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (eU : T.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (schemeModuleCanonicalFiberProjection (j ≫ U.ι) T)) := by
  let i := j ≫ U.ι
  let R := Scheme.Modules.restrictFunctor U.ι
  let O := SheafOfModules.unit X.ringCatSheaf
  let A := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let p := schemeModuleCanonicalFiberProjection i T
  let mu := schemeModuleTensorUnitLeftIso T
  let n := schemeModuleTensorRestrictNatIsoOfLocalTrivialization U T eU
  let uO := Scheme.Modules.restrictUnitIso U.ι
  let eT : R.obj T ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    (R.mapIso mu).symm ≪≫ n.app O ≪≫ uO
  let k := restrictPushforwardUnitFactorThroughOpenIso j U.ι
  let eC := n.app A ≪≫ k
  let eF := R.mapIso ((Scheme.Modules.pushforward i).mapIso
    (schemeModuleFiberFrameIso U.ι j T eT)) ≪≫ k
  have hcover : (Opens.grothendieckTopology X).CoversTop B := by
    apply (Opens.coversTop_iff X B).mpr
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hB x⟩
  let S := closedImmersionIdealTwistSequence i T
  have hS : S.ShortExact := closedImmersionIdealTwistSequence_shortExact_of_coversTop_iso_unit
    i B hcover eB
  have hSR := ShortComplex.shortExact_map_restrictFunctor U.ι S hS
  letI : Epi (R.map (schemeModuleTensorMap q (𝟙 T))) := by
    change Epi (S.map R).g
    exact hSR.epi_g
  have hn := n.hom.naturality q
  change R.map (schemeModuleTensorMap q (𝟙 T)) ≫ (n.app A).hom =
    (n.app O).hom ≫ R.map q at hn
  have hchart : R.map mu.hom ≫ eT.hom = (n.app O).hom ≫ uO.hom := by
    change (R.mapIso mu).hom ≫
      ((R.mapIso mu).inv ≫ (n.app O).hom ≫ uO.hom) = _
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hq := cubicClosedPointSerreSurfaceJetCotangent_closedQuotient_openRestriction U.ι j
  have hqC : R.map (schemeModuleTensorMap q (𝟙 T)) ≫ eC.hom =
      R.map mu.hom ≫ eT.hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j := by
    calc
      _ = ((n.app O).hom ≫ R.map q) ≫ k.hom := by
        change R.map (schemeModuleTensorMap q (𝟙 T)) ≫
          ((n.app A).hom ≫ k.hom) = _
        rw [← Category.assoc, hn]
      _ = (n.app O).hom ≫ uO.hom ≫
          IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j := by
        rw [Category.assoc, hq]
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun a => a ≫ IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j) hchart.symm
  have hp := congrArg R.map (schemeModuleCanonicalFiberProjection_unit_square i T)
  rw [R.map_comp, R.map_comp] at hp
  have hf : R.map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T) ≫
      eF.hom = eT.hom ≫ IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j :=
    schemeModuleFiberFrameIso_restrict_unit_square U.ι j T eT
  have heq : R.map p ≫ eF.hom = eC.hom := by
    apply (cancel_epi (R.map (schemeModuleTensorMap q (𝟙 T)))).mp
    calc
      _ = (R.map mu.hom ≫
          R.map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T)) ≫ eF.hom := by
        rw [← Category.assoc, hp]
      _ = R.map mu.hom ≫ (eT.hom ≫
          IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j) := by
        rw [Category.assoc, hf]
      _ = R.map (schemeModuleTensorMap q (𝟙 T)) ≫ eC.hom := by
        rw [← Category.assoc]
        exact hqC.symm
  letI : IsIso (R.map p ≫ eF.hom) := by rw [heq]; infer_instance
  exact IsIso.of_isIso_comp_right (R.map p) eF.hom

/-- Global invertibility of the actual canonical projection. On the genuine
unit chart it is the same quotient; elsewhere BOTH stalks vanish from actual
closed support. Ordinary rank-one chart geometry is the only extra input. -/
theorem schemeModuleCanonicalFiberProjection_isIso_of_factor_unitCharts
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)] (T : X.Modules)
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, T.over (B x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (eU : T.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    IsIso (schemeModuleCanonicalFiberProjection (j ≫ U.ι) T) := by
  let i := j ≫ U.ι
  let p := schemeModuleCanonicalFiberProjection i T
  have hcover : (Opens.grothendieckTopology X).CoversTop B := by
    apply (Opens.coversTop_iff X B).mpr
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hB x⟩
  apply schemeModuleMap_isIso_of_stalk p
  intro x
  by_cases hx : x ∈ U
  · letI : IsIso ((Scheme.Modules.restrictFunctor U.ι).map p) :=
      schemeModuleCanonicalFiberProjection_restrict_isIso_of_unitCharts U j T B hB eB eU
    exact schemeModuleStalkMap_isIso_of_restrict U ⟨x, hx⟩ p
  · have hoff : x ∉ Set.range i := by
      rintro ⟨z, hz⟩
      apply hx
      rw [← hz]
      exact (j z).property
    have hsrc := closedImmersionPushforwardTwist_stalk_subsingleton_off_range_of_coversTop_iso_unit
      i T B hcover eB x hoff
    have htgt := schemeModulePushforward_stalk_subsingleton_off_range i
      ((Scheme.Modules.pullback i).obj T) x hoff
    let A := (schemeModuleStalkModuleFunctor X x).obj
      (schemeModuleTensor ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) T)
    let C := (schemeModuleStalkModuleFunctor X x).obj
      ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T))
    letI : Subsingleton A := by
      change Subsingleton ((schemeModuleTensor ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) T).presheaf.stalk x)
      exact hsrc
    letI : Subsingleton C := by
      change Subsingleton (((Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj T)).presheaf.stalk x)
      exact htgt
    have hA : IsZero A := ModuleCat.isZero_of_subsingleton A
    have hC : IsZero C := ModuleCat.isZero_of_subsingleton C
    let v : A ≅ C := hA.iso hC
    have hv : (schemeModuleStalkModuleFunctor X x).map p = v.hom := hA.eq_of_src _ _
    rw [hv]
    infer_instance

/-- The actual canonical projection Iso, with its original map as hom. -/
def schemeModuleCanonicalFiberIso_of_factor_unitCharts
    {Z : Scheme.{u}} (U : X.Opens) (j : Z ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)] (T : X.Modules)
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, T.over (B x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (eU : T.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    schemeModuleTensor ((Scheme.Modules.pushforward (j ≫ U.ι)).obj
      (SheafOfModules.unit Z.ringCatSheaf)) T ≅
      (Scheme.Modules.pushforward (j ≫ U.ι)).obj ((Scheme.Modules.pullback (j ≫ U.ι)).obj T) := by
  letI := schemeModuleCanonicalFiberProjection_isIso_of_factor_unitCharts U j T B hB eB eU
  exact asIso (schemeModuleCanonicalFiberProjection (j ≫ U.ι) T)

/-- The SAME actual projection preserves the original pi-induced ground
constants on every actual open. Its scalar law is the actual O-linear
component law, not a scalar structure transported through a chosen Iso. -/
theorem schemeModuleCanonicalFiberProjection_originalBaseConstant
    {K : Type u} [Field K] (pi : X ⟶ Spec (CommRingCat.of K))
    {Z : Scheme.{u}} (i : Z ⟶ X) (T : X.Modules) (W : X.Opens) (c : K)
    (s : (schemeModuleTensor ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) T).val.obj (Opposite.op W)) :
    (schemeModuleCanonicalFiberProjection i T).val.app (Opposite.op W)
        (schemeOpenBaseRingHom pi W c • s) =
      schemeOpenBaseRingHom pi W c •
        (schemeModuleCanonicalFiberProjection i T).val.app (Opposite.op W) s :=
  ((schemeModuleCanonicalFiberProjection i T).val.app (Opposite.op W)).hom.map_smul
    (schemeOpenBaseRingHom pi W c) s

end PfaffianDescent

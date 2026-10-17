import PfaffianDescent.CorayOpenPullbackAdjunctionCoherence
import PfaffianDescent.SchemeModuleRankOneCanonicalFiberIso
import PfaffianDescent.CorayOwnCartierResidueSequence

/-!
The ORIGINAL canonical projection is invertible for every closed immersion
and actual rank-one coefficient, without requiring its entire support to lie
in one unit chart. Actual Cartesian restriction, native unit coherence and
epi cancellation identify the map; stalks glue its local invertibility.
SOURCE ONLY / UNVERIFIED; root owns all compiler and acceptance checks.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- On every actual coefficient unit chart, the same canonical projection
is the actual structure quotient after the two genuine frames. The source
uses the true inverse-image open, so no whole-support factorization is input. -/
theorem schemeModuleCanonicalFiberProjection_restrict_isIso_of_rankOneCharts
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, T.over (B x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (U : X.Opens)
    (eU : T.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (schemeModuleCanonicalFiberProjection i T)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let J := Scheme.Modules.pushforward (i ∣_ U)
  let O := SheafOfModules.unit X.ringCatSheaf
  let A := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let p := schemeModuleCanonicalFiberProjection i T
  let mu := schemeModuleTensorUnitLeftIso T
  let n := schemeModuleTensorRestrictNatIsoOfLocalTrivialization U T eU
  let uO := Scheme.Modules.restrictUnitIso U.ι
  let eT : R.obj T ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    (R.mapIso mu).symm ≪≫ n.app O ≪≫ uO
  let k := schemeModuleOpenPushforwardUnitBaseChangeIso i U
  let eC := n.app A ≪≫ k
  let eF := schemeModuleOpenPushforwardBaseChangeIso i U
      ((Scheme.Modules.pullback i).obj T) ≪≫
    J.mapIso (schemeModuleOpenAdjunctionUnitFrameIso i U T eT)
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
  have hq := schemeModuleOpenPushforwardUnitBaseChange_quotient_square i U
  have hqC : R.map (schemeModuleTensorMap q (𝟙 T)) ≫ eC.hom =
      R.map mu.hom ≫ eT.hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ∣_ U) := by
    calc
      _ = ((n.app O).hom ≫ R.map q) ≫ k.hom := by
        change R.map (schemeModuleTensorMap q (𝟙 T)) ≫
          ((n.app A).hom ≫ k.hom) = _
        rw [← Category.assoc, hn]
      _ = (n.app O).hom ≫ uO.hom ≫
          IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ∣_ U) := by
        rw [Category.assoc, hq]
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun a => a ≫ IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ∣_ U))
          hchart.symm
  have hp := congrArg R.map (schemeModuleCanonicalFiberProjection_unit_square i T)
  rw [R.map_comp, R.map_comp] at hp
  have hf : R.map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T) ≫
      eF.hom = eT.hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ∣_ U) := by
    change R.map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T) ≫
      ((schemeModuleOpenPushforwardBaseChangeIso i U
        ((Scheme.Modules.pullback i).obj T)).hom ≫
        J.map (schemeModuleOpenAdjunctionUnitFrameIso i U T eT).hom) = _
    exact schemeModuleOpenAdjunctionUnitFrameIso_unit_square i U T eT
  have heq : R.map p ≫ eF.hom = eC.hom := by
    apply (cancel_epi (R.map (schemeModuleTensorMap q (𝟙 T)))).mp
    calc
      _ = (R.map mu.hom ≫
          R.map ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T)) ≫ eF.hom := by
        rw [← Category.assoc, hp]
      _ = R.map mu.hom ≫ (eT.hom ≫
          IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ∣_ U)) := by
        rw [Category.assoc, hf]
      _ = R.map (schemeModuleTensorMap q (𝟙 T)) ≫ eC.hom := by
        rw [← Category.assoc]
        exact hqC.symm
  letI : IsIso (R.map p ≫ eF.hom) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_right (R.map p) eF.hom

/-- Actual coefficient charts glue invertibility on every original stalk.
The map remains the original tensor/pushforward projection throughout. -/
theorem schemeModuleCanonicalFiberProjection_isIso_of_locallyRankOne
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) (hT : schemeModuleLocallyRankOne T) :
    IsIso (schemeModuleCanonicalFiberProjection i T) := by
  classical
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts T hT
  apply schemeModuleMap_isIso_of_stalk (schemeModuleCanonicalFiberProjection i T)
  intro x
  letI : IsIso ((Scheme.Modules.restrictFunctor (B x).ι).map
      (schemeModuleCanonicalFiberProjection i T)) :=
    schemeModuleCanonicalFiberProjection_restrict_isIso_of_rankOneCharts
      i T B hB eB (B x) (eB x)
  exact schemeModuleStalkMap_isIso_of_restrict (B x) ⟨x, hB x⟩
    (schemeModuleCanonicalFiberProjection i T)

/-- The OWN actual Cartier residue quotient identifies with pushforward
of the actual pulled-back coefficient/ideal-dual. Both rank-one hypotheses
are internally derived from H and the ordinary coefficient line geometry. -/
def RegularPrincipalImmersion.actualCartierResidueProjectionIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    (H.actualCartierResidueSequence W).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj
          (schemeModuleTensor W
            (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)))) := by
  let M := IdealSheafDataModule.closedImmersionModule i
  let T := schemeModuleTensor W (SchemeModuleInternalHom.dual M)
  have hT : schemeModuleLocallyRankOne T :=
    schemeModuleLocallyRankOne_tensor W (SchemeModuleInternalHom.dual M) hW
      (schemeModuleLocallyRankOne_dual M H.inverseCartierTwist_locallyRankOne)
  letI : IsIso (schemeModuleCanonicalFiberProjection i T) :=
    schemeModuleCanonicalFiberProjection_isIso_of_locallyRankOne i T hT
  change schemeModuleTensor ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) T ≅
    (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T)
  exact asIso (schemeModuleCanonicalFiberProjection i T)

end PfaffianDescent
end

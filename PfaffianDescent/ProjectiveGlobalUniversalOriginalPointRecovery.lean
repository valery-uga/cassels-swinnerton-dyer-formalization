import PfaffianDescent.ProjectiveChartGlobalUniversalFamilyPullback
import PfaffianDescent.NativeRelativeCartesianPointNaturality317
import PfaffianDescent.NativeOriginalClosedPointFibre317

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false

variable {J : Type u} {X B : Scheme.{u}} (F : X ⟶ B) (U : J → X.Opens) (n : ℕ)
variable [IsSeparated F] (H : J → Over B)
variable (eta : ∀ i, relativeFiniteFlatHilbertFunctor197 ((U i).ι ≫ F) n ≅ yoneda.obj (H i))

/-- Exact reduction of the ACTUAL constructed global universal pullback
recovers the original field chart family. No reduced-support replacement
or supplied lifted-family equality is used. -/
theorem relativeOpenChartGlobalUniversalPullback_reductionToChart001
    {T0 T1 : Over B} (a : T0 ⟶ T1)
    (g : T1 ⟶ relativeOpenChartParameterGluedObject001 F U n H eta)
    (i : J) (g0 : T0 ⟶ H i)
    (hReduction : a ≫ g = g0 ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i) :
    (relativeFiniteFlatHilbertFunctor197 F n).map a.op
      (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T1 g) =
      relativeOpenChartClassifiedAmbientPoint001 F (U i) n (H i) (eta i) T0 g0 := by
  have hNatural := relativeOpenChartParameterGlobalUniversalFamilyPullback_natural001
    F U n H eta a g
  have hClassifier := congrArg
    (fun q : T0 ⟶ relativeOpenChartParameterGluedObject001 F U n H eta =>
      relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T0 q) hReduction
  exact hNatural.symm.trans (hClassifier.trans
    (relativeOpenChartParameterGlobalUniversalFamilyPullback_chartRecovery001 F U n H eta i T0 g0))

/-- The reduction equality is equality of the complete ideal sheaves,
including every nilpotent, in the literal relative197 ambient scheme. -/
theorem relativeOpenChartGlobalUniversalPullback_reductionToChart_wholeIdeal001
    {T0 T1 : Over B} (a : T0 ⟶ T1)
    (g : T1 ⟶ relativeOpenChartParameterGluedObject001 F U n H eta)
    (i : J) (g0 : T0 ⟶ H i)
    (hReduction : a ≫ g = g0 ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i) :
    (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T1 g).val.comap
        (relativeHilbertAmbientMap197 F a) =
      (relativeOpenChartClassifiedAmbientPoint001 F (U i) n (H i) (eta i) T0 g0).val := by
  have h := relativeOpenChartGlobalUniversalPullback_reductionToChart001 F U n H eta a g i g0 hReduction
  exact (relativeFiniteFlatHilbertFunctor197_map_ideal F n a
    (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T1 g)).symm.trans
      (congrArg Subtype.val h)

/-- The physical family is CONSTRUCTED FROM the global universal family.
The actual Cartesian ambient comparison only changes its ambient scheme;
no local317 lifted family or physical-family outcome is supplied. -/
def relativeOpenChartGlobalUniversalPhysicalFamily001
    (T : Over B) {Y : Scheme.{u}} (aY : Y ⟶ X) (fY : Y ⟶ T.left)
    (hY : IsPullback aY fY F T.hom)
    (g : T ⟶ relativeOpenChartParameterGluedObject001 F U n H eta) :
    FiniteFlatHilbertPoint195 fY n :=
  (nativeRelativeCartesianPointEquiv317 F T aY fY hY n).symm
    (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T g)

/-- Exact whole ideal of the physical family, as comap of the ACTUAL
global universal whole ideal along the original ambient maps. -/
theorem relativeOpenChartGlobalUniversalPhysicalFamily_wholeIdeal001
    (T : Over B) {Y : Scheme.{u}} (aY : Y ⟶ X) (fY : Y ⟶ T.left)
    (hY : IsPullback aY fY F T.hom)
    (g : T ⟶ relativeOpenChartParameterGluedObject001 F U n H eta) :
    (relativeOpenChartGlobalUniversalPhysicalFamily001 F U n H eta T aY fY hY g).val =
      (relativeOpenChartParameterGlobalUniversalWholeIdeal001 F U n H eta).comap
        ((nativeRelativeCartesianChartIso317 F T aY fY hY).hom ≫ relativeHilbertAmbientMap197 F g) := by
  have hPhysical :
      (relativeOpenChartGlobalUniversalPhysicalFamily001 F U n H eta T aY fY hY g).val =
      (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T g).val.comap
        (nativeRelativeCartesianChartIso317 F T aY fY hY).hom := rfl
  have hUniversal := congrArg
    (fun I : (pullback T.hom F).IdealSheafData =>
      I.comap (nativeRelativeCartesianChartIso317 F T aY fY hY).hom)
    (relativeOpenChartParameterGlobalUniversalFamilyPullback_wholeIdeal001 F U n H eta T g)
  exact hPhysical.trans (hUniversal.trans
    ((relativeOpenChartParameterGlobalUniversalWholeIdeal001 F U n H eta).comap_comp
      (nativeRelativeCartesianChartIso317 F T aY fY hY).hom
      (relativeHilbertAmbientMap197 F g)).symm)

/-- The original field seed identifies the SAME original P ideal. The
actual global classifier reduction and original Cartesian ambient diagrams
then DERIVE the lifted physical family's exact P fibre, including its
nilpotents. No lifted whole-ideal or original-P Cartesian outcome is a premise. -/
theorem relativeOpenChartGlobalUniversalPhysicalFamily_originalPoint_wholeReduction001
    {T0 T1 : Over B} (a : T0 ⟶ T1)
    {Y0 Y1 : Scheme.{u}}
    (a0 : Y0 ⟶ X) (f0 : Y0 ⟶ T0.left) (h0 : IsPullback a0 f0 F T0.hom)
    (a1 : Y1 ⟶ X) (f1 : Y1 ⟶ T1.left) (h1 : IsPullback a1 f1 F T1.hom)
    (d : Y0 ⟶ Y1) (ha : d ≫ a1 = a0) (hf : d ≫ f1 = f0 ≫ a.left)
    (g : T1 ⟶ relativeOpenChartParameterGluedObject001 F U n H eta)
    (i : J) (g0 : T0 ⟶ H i)
    (hReduction : a ≫ g = g0 ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)
    (P : closedPoints Y0)
    (hPointSeed :
      (relativeOpenChartClassifiedAmbientPoint001 F (U i) n (H i) (eta i) T0 g0).val.comap
        (nativeRelativeCartesianChartIso317 F T0 a0 f0 h0).hom = (Y0.fromSpecResidueField P.val).ker) :
    (relativeOpenChartGlobalUniversalPhysicalFamily001 F U n H eta T1 a1 f1 h1 g).val.comap d =
      (Y0.fromSpecResidueField P.val).ker := by
  let Q := relativeOpenChartGlobalUniversalPhysicalFamily001 F U n H eta T1 a1 f1 h1 g
  let Qrel := relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T1 g
  let e0 := nativeRelativeCartesianChartIso317 F T0 a0 f0 h0
  let e1 := nativeRelativeCartesianChartIso317 F T1 a1 f1 h1
  have hQ : Q.val = Qrel.val.comap e1.hom := rfl
  have hDiagram : e0.hom ≫ relativeHilbertAmbientMap197 F a = d ≫ e1.hom :=
    nativeRelativeCartesianChartIso_natural317 F a a0 f0 h0 a1 f1 h1 d ha hf
  have hRelative := relativeOpenChartGlobalUniversalPullback_reductionToChart_wholeIdeal001
    F U n H eta a g i g0 hReduction
  exact (congrArg (fun I : Y1.IdealSheafData => I.comap d) hQ).trans
    ((Qrel.val.comap_comp d e1.hom).symm.trans
      ((congrArg Qrel.val.comap hDiagram.symm).trans
        ((Qrel.val.comap_comp e0.hom (relativeHilbertAmbientMap197 F a)).trans
          ((congrArg
            (fun I : (pullback T0.hom F).IdealSheafData => I.comap e0.hom) hRelative).trans hPointSeed))))

/-- Construct the literal ORIGINAL-P-to-global-universal-family map and
Cartesian special-fibre square from the proved whole-ideal reduction. -/
theorem relativeOpenChartGlobalUniversalPhysicalFamily_originalPoint_isPullback001
    {T0 T1 : Over B} (a : T0 ⟶ T1)
    {Y0 Y1 : Scheme.{u}}
    (a0 : Y0 ⟶ X) (f0 : Y0 ⟶ T0.left) (h0 : IsPullback a0 f0 F T0.hom)
    (a1 : Y1 ⟶ X) (f1 : Y1 ⟶ T1.left) (h1 : IsPullback a1 f1 F T1.hom)
    (d : Y0 ⟶ Y1) (ha : d ≫ a1 = a0) (hf : d ≫ f1 = f0 ≫ a.left)
    (g : T1 ⟶ relativeOpenChartParameterGluedObject001 F U n H eta)
    (i : J) (g0 : T0 ⟶ H i)
    (hReduction : a ≫ g = g0 ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)
    (P : closedPoints Y0)
    (hPointSeed :
      (relativeOpenChartClassifiedAmbientPoint001 F (U i) n (H i) (eta i) T0 g0).val.comap
        (nativeRelativeCartesianChartIso317 F T0 a0 f0 h0).hom = (Y0.fromSpecResidueField P.val).ker) :
    let Q := relativeOpenChartGlobalUniversalPhysicalFamily001 F U n H eta T1 a1 f1 h1 g
    ∃ u0 : Spec (Y0.residueField P.val) ⟶ Q.val.subscheme,
      IsPullback u0 (Y0.fromSpecResidueField P.val) Q.val.subschemeι d := by
  intro Q
  have hPoint : Q.val.comap d = (Y0.fromSpecResidueField P.val).ker :=
    relativeOpenChartGlobalUniversalPhysicalFamily_originalPoint_wholeReduction001
      F U n H eta a a0 f0 h0 a1 f1 h1 d ha hf g i g0 hReduction P hPointSeed
  exact ⟨nativeOriginalClosedPointFibreMap317 Q.val d P hPoint,
    nativeOriginalClosedPointFibreMap_isPullback317 Q.val d P hPoint⟩

end PfaffianDescent
end

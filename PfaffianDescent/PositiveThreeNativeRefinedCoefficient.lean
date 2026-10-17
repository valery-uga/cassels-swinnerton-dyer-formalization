import PfaffianDescent.PositiveThreeNativePowerFrame
import PfaffianDescent.NativeOpenPullbackFramedSection
import PfaffianDescent.NativeRefinedPullbackFramedCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentRefinedSectionCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentSectionChartCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartRefinement
import PfaffianDescent.AffineQuotientPushforwardTilde

/-! SOURCE ONLY. Canonical native O(3) coefficient and whole chart scalar
map under the ORIGINAL power frame. Generic degree-one generation is the
ordinary grading input; the original Bool quotient caller derives it. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory HomogeneousLocalization Opposite
open AllCharacteristics.HomogeneousProjective BundleSectionZeroLocus
universe u
variable {A ρ : Type u} [CommRing A] [SetLike ρ A] [AddSubgroupClass ρ A]
variable (G : ℕ → ρ) [GradedRing G]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] isIso_pullbackUnitComparison

private instance nativePowerChartUnitComparison_isIso (f : A) (hf : f ∈ G 1) :
    IsIso (pullbackUnitComparison (Proj.awayι G f hf Nat.zero_lt_one)) :=
  isIso_pullbackUnitComparison (Proj.awayι G f hf Nat.zero_lt_one)

/-- Actual cubic-power maps are literal homogeneous-section maps, as whole
original morphisms, derived from the native all-open value identity. -/
private lemma nativePowerFrame_eq_homogeneousSectionMap (eta : G 1) :
    positiveThreePowerFrameHom G eta =
      (positiveSheafOfModules G 3).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous G 3 (degreeOnePower G eta 3)) := by
  apply (positiveSheafOfModules G 3).unitHomEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  simpa only [SheafOfModules.unitHomEquiv_apply_coe] using
    positiveThreePowerFrameHom_one_eq_homogeneousSection G eta U.unop

/-- Actual homogeneous-section coefficient in the original local power
frame, as an original structure-sheaf section on the WHOLE basic open. -/
theorem positiveThreePowerFrame_localUnitHomogeneousCoefficient
    (ell : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) (q : G 3) :
    schemeModuleLocalUnitSectionAddEquiv (Proj.basicOpen G (ell : A))
      (positiveSheafOfModules G 3)
      (positiveThreePowerFrameRestrictionUnitIso G ell hspan)
      ((positiveGlobalSectionOfHomogeneous G 3 q).val
        (op (Proj.basicOpen G (ell : A)))) =
    (Proj.awayToSection G (ell : A)).hom
      (Away.mk G ell.2 3 (q : A) (by simpa using q.property)) := by
  let U := Proj.basicOpen G (ell : A)
  let T := positiveSheafOfModules G 3
  let a := positiveThreePowerFrameHom G ell
  letI := positiveThreePowerFrameHom_restrict_isIso G ell hspan
  let e := asIso ((Scheme.Modules.restrictFunctor U.ι).map a)
  let v := Scheme.Modules.restrictUnitIso U.ι
  have he : positiveThreePowerFrameRestrictionUnitIso G ell hspan ≪≫ v.symm = e.symm := by
    change (e.symm ≪≫ v) ≪≫ v.symm = e.symm
    exact (Iso.trans_assoc e.symm v v.symm).trans
      ((congrArg (fun z => e.symm ≪≫ z) (Iso.self_symm_id v)).trans (Iso.trans_refl e.symm))
  let E := schemeModuleLocalSectionAddEquiv U
    (SheafOfModules.unit (Proj G).ringCatSheaf) T e
  unfold schemeModuleLocalUnitSectionAddEquiv
  rw [he]
  change E.symm _ = _
  apply E.injective
  rw [E.apply_symm_apply]
  change _ = (schemeModuleRestrictTopSectionIso U T).hom
    (((Scheme.Modules.toPresheaf (U : Scheme)).map
      ((Scheme.Modules.restrictFunctor U.ι).map a)).app (op ⊤)
        ((schemeModuleRestrictTopSectionIso U
          (SheafOfModules.unit (Proj G).ringCatSheaf)).inv _))
  rw [cubicClosedPointSerreSurfaceJetCotangent_restrictTopSectionIso_map]
  exact (positiveThreePowerFrameHom_awayCoefficient_section G ell q).symm

/-- The native whole local framed Hom has exactly that actual fraction
coefficient; no chart action or coefficient is supplied as a hypothesis. -/
theorem positiveThreePowerFrame_unitHomogeneousCoefficient
    (ell : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) (q : G 3) :
    unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso (Proj.basicOpen G (ell : A)).ι).inv ≫
        (Scheme.Modules.restrictFunctor (Proj.basicOpen G (ell : A)).ι).map
          ((positiveSheafOfModules G 3).unitHomEquiv.symm
            (positiveGlobalSectionOfHomogeneous G 3 q)) ≫
        (positiveThreePowerFrameRestrictionUnitIso G ell hspan).hom) =
    (Proj.basicOpen G (ell : A)).topIso.inv
      ((Proj.awayToSection G (ell : A)).hom
        (Away.mk G ell.2 3 (q : A) (by simpa using q.property))) := by
  have h := cubicClosedPointSerreSurfaceJetCotangent_sectionChartCoefficient
    (Proj.basicOpen G (ell : A)) (positiveSheafOfModules G 3)
    (positiveThreePowerFrameRestrictionUnitIso G ell hspan)
    (positiveGlobalSectionOfHomogeneous G 3 q)
  exact h.trans (congrArg (fun z => (Proj.basicOpen G (ell : A)).topIso.inv z)
    (positiveThreePowerFrame_localUnitHomogeneousCoefficient G ell hspan q))

/-- Original basicOpenIsoSpec transports the actual away fraction to its
original Spec global section. This is generic in the SAME grading. -/
theorem nativeBasicOpenIsoSpec_inv_appTop_awaySection
    (ell : G 1) (a : Away G (ell : A)) :
    (Proj.basicOpenIsoSpec G (ell : A) ell.property Nat.zero_lt_one).inv.appTop
      ((Proj.basicOpen G (ell : A)).topIso.inv
        ((ProjectiveSpectrum.Proj.awayToSection G (ell : A)).hom a)) =
    (Scheme.ΓSpecIso (.of (Away G (ell : A)))).inv.hom a := by
  let U := Proj.basicOpen G (ell : A)
  let e := Proj.basicOpenIsoSpec G (ell : A) ell.property Nat.zero_lt_one
  let v := (Scheme.ΓSpecIso (.of (Away G (ell : A)))).inv a
  have hh : e.hom.appTop v = U.topIso.inv
      ((ProjectiveSpectrum.Proj.awayToSection G (ell : A)).hom a) := by
    change (Proj.basicOpenToSpec G (ell : A)).app ⊤ v = _
    rw [Proj.basicOpenToSpec_app_top]
    simp only [ConcreteCategory.comp_apply]
    exact congrArg (fun z => U.topIso.inv
      ((ProjectiveSpectrum.Proj.awayToSection G (ell : A)).hom z))
      (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of (Away G (ell : A)))) a)
  have hc : e.hom.appTop ≫ e.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]
    simp
  have hv := congrArg (fun m => m.hom v) hc
  change e.inv.appTop _ = v
  exact (congrArg (fun z => e.inv.appTop z) hh).symm.trans hv

/-- Canonical actual native chart frame built from the original power map. -/
def positiveThreePowerFrame_nativeChartUnitIso
    (ell : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) :
    (Scheme.Modules.pullback (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)).obj
      (positiveSheafOfModules G 3) ≅
      SheafOfModules.unit (Spec (.of (Away G (ell : A)))).ringCatSheaf := by
  let U := Proj.basicOpen G (ell : A)
  let e := Proj.basicOpenIsoSpec G (ell : A) ell.property Nat.zero_lt_one
  let T := positiveSheafOfModules G 3
  let p := positiveThreePowerFrameRestrictionUnitIso G ell hspan
  let pR := cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv T p
  exact (Scheme.Modules.restrictFunctorIsoPullback (Proj.awayι G (ell : A)
    ell.property Nat.zero_lt_one)).symm.app T ≪≫ pR

/-- Bounded native coefficient of ANY original homogeneous cubic section
under the SAME original power frame, derived through generic actual refinement. -/
theorem positiveThreePowerFrame_nativeChart_homogeneousCoefficient
    (ell : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) (q : G 3) :
    unitEndomorphismValue
      (inv (I := isIso_pullbackUnitComparison
          (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one))
        (pullbackUnitComparison (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)) ≫
        (Scheme.Modules.pullback (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)).map
          ((positiveSheafOfModules G 3).unitHomEquiv.symm
            (positiveGlobalSectionOfHomogeneous G 3 q)) ≫
        (positiveThreePowerFrame_nativeChartUnitIso G ell hspan).hom) =
    (Scheme.ΓSpecIso (.of (Away G (ell : A)))).inv.hom
      (Away.mk G ell.property 3 (q : A) (by simpa using q.property)) := by
  let U := Proj.basicOpen G (ell : A)
  let e := Proj.basicOpenIsoSpec G (ell : A) ell.property Nat.zero_lt_one
  let T := positiveSheafOfModules G 3
  let p := positiveThreePowerFrameRestrictionUnitIso G ell hspan
  let s := T.unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous G 3 q)
  have h := nativeRefinedPullbackFramedCoefficient U e.inv T p s
  have hOld := positiveThreePowerFrame_unitHomogeneousCoefficient G ell hspan q
  have hTransport := congrArg (fun z => e.inv.appTop z) hOld
  exact h.trans (hTransport.trans (nativeBasicOpenIsoSpec_inv_appTop_awaySection G ell _))

/-- Exact native chart coefficient of the ORIGINAL other cubic-power map. -/
theorem positiveThreePowerFrame_nativeChart_coordinateCoefficient
    (ell eta : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) :
    unitEndomorphismValue
      (inv (I := isIso_pullbackUnitComparison
          (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one))
        (pullbackUnitComparison (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)) ≫
        (Scheme.Modules.pullback (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)).map
          (positiveThreePowerFrameHom G eta) ≫
        (positiveThreePowerFrame_nativeChartUnitIso G ell hspan).hom) =
    (Scheme.ΓSpecIso (.of (Away G (ell : A)))).inv.hom
      (Away.mk G ell.property 3 ((degreeOnePower G eta 3 : G 3) : A)
        (by simpa only [smul_eq_mul, mul_one] using (degreeOnePower G eta 3).property)) := by
  exact (nativePullbackFramedCoefficient_congr
    (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one) (positiveSheafOfModules G 3)
    (positiveThreePowerFrame_nativeChartUnitIso G ell hspan)
    (positiveThreePowerFrameHom G eta)
    ((positiveSheafOfModules G 3).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous G 3 (degreeOnePower G eta 3)))
    (nativePowerFrame_eq_homogeneousSectionMap G eta)).trans
      (positiveThreePowerFrame_nativeChart_homogeneousCoefficient G ell hspan
        (degreeOnePower G eta 3))

/-- WHOLE actual unit scalar action of that original power map, retaining
its actual localization section rather than merely its numerical degree. -/
theorem positiveThreePowerFrame_nativeChart_coordinateUnitScalar
    (ell eta : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) :
    inv (I := isIso_pullbackUnitComparison
          (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one))
        (pullbackUnitComparison (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)) ≫
        (Scheme.Modules.pullback (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)).map
          (positiveThreePowerFrameHom G eta) ≫
        (positiveThreePowerFrame_nativeChartUnitIso G ell hspan).hom =
    unitEndomorphismOfRegularFunction
      ((Scheme.ΓSpecIso (.of (Away G (ell : A)))).inv.hom
        (Away.mk G ell.property 3 ((degreeOnePower G eta 3 : G 3) : A)
          (by simpa only [smul_eq_mul, mul_one] using (degreeOnePower G eta 3).property))) := by
  letI : IsIso (pullbackUnitComparison
      (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)) :=
    isIso_pullbackUnitComparison
      (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)
  calc
    _ = unitEndomorphismOfRegularFunction (unitEndomorphismValue
      (inv (pullbackUnitComparison (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)) ≫
        (Scheme.Modules.pullback (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)).map
          (positiveThreePowerFrameHom G eta) ≫
        (positiveThreePowerFrame_nativeChartUnitIso G ell hspan).hom)) :=
      (unitEndomorphismOfRegularFunction_value _).symm
    _ = _ := congrArg unitEndomorphismOfRegularFunction
      (positiveThreePowerFrame_nativeChart_coordinateCoefficient G ell eta hspan)

end PfaffianDescent.ProjectiveNegativeTwist

import PfaffianDescent.TwistedCubicNativeGlobalPositiveThreeIso
import PfaffianDescent.PositiveThreeNativeRefinedCoefficient
import PfaffianDescent.QuarticTwistedCubicResidual
import AllCharacteristics.SpecGlobalSectionEvaluation

/-! SOURCE ONLY. The SAME native global comparison carries ALL FOUR actual
pulled coordinate maps to the literal parametrizing cubic-section maps.
Every coordinate ratio and whole local-map comparison is derived internally.
No frame, transition, complete-series, H0 or desired image certificate is input. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist HomogeneousLocalization
open BundleSectionZeroLocus SchemeModuleInternalHom
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "M" => CategoryTheory.Functor.obj (Scheme.Modules.pullback
  (standardProjectiveLineToTwistedCubic (K := K))) (positiveSheafOfModules (grading I) 1)
local notation "N" => positiveSheafOfModules (grading L) 3

/-- Literal original polynomial parametrization, with only canonical
Fin2-to-Bool renaming to the SAME original quotient projective line. -/
def standardTwistedCubicLiteralLinePolynomial (k : Fin 4) : homogeneousSubmodule Bool K 3 :=
  ⟨rename finTwoEquiv (standardTwistedCubicParam K (X k)), by
    have h := standardTwistedCubicParam_homogeneous (isHomogeneous_X K k)
    have h' : (standardTwistedCubicParam K (X k)).IsHomogeneous 3 := by
      simpa only [Nat.mul_one] using h
    exact h'.rename_isHomogeneous⟩

/-- The image of that literal polynomial under the original quotient map. -/
def standardTwistedCubicLiteralLineCubic (k : Fin 4) : grading L 3 :=
  ⟨quotientGradedRingHom L (standardTwistedCubicLiteralLinePolynomial (K := K) k),
    (quotientGradedRingHom L).2 (standardTwistedCubicLiteralLinePolynomial (K := K) k).2⟩

/-- The genuine whole native section-map associated to that SAME cubic. -/
def standardTwistedCubicLiteralLineSectionHom (k : Fin 4) :
    SheafOfModules.unit (scheme L).ringCatSheaf ⟶ N :=
  (positiveSheafOfModules (grading L) 3).unitHomEquiv.symm
    (positiveGlobalSectionOfHomogeneous (grading L) 3
      (standardTwistedCubicLiteralLineCubic (K := K) k))

private theorem literalLineCubic_raw (k : Fin 4) :
    (standardTwistedCubicLiteralLineCubic (K := K) k : CoordinateRing L) =
      (![coordinate L false ^ 3,
        coordinate L false ^ 2 * coordinate L true,
        coordinate L false * coordinate L true ^ 2,
        coordinate L true ^ 3] : Fin 4 → CoordinateRing L) k := by
  fin_cases k <;>
    simp [standardTwistedCubicLiteralLineCubic, standardTwistedCubicLiteralLinePolynomial,
      standardTwistedCubicParam, finTwoEquiv, quotientGradedRingHom_coordinate]

private theorem nativeAway_threeProduct
    {A ρ : Type u} [CommRing A] [SetLike ρ A] [AddSubgroupClass ρ A]
    (G : ℕ → ρ) [GradedRing G] (ell x y z : G 1) (q : G 3)
    (hq : (q : A) = (x : A) * (y : A) * (z : A)) :
    Away.mk G ell.property 3 (q : A) (by simpa using q.property) =
      Away.mk G ell.property 1 (x : A) (by simpa using x.property) *
      Away.mk G ell.property 1 (y : A) (by simpa using y.property) *
      Away.mk G ell.property 1 (z : A) (by simpa using z.property) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, Away.val_mk, hq, Localization.mk_mul,
    pow_one]
  apply congrArg (fun d : Submonoid.powers (ell : A) =>
    Localization.mk ((x : A) * (y : A) * (z : A)) d)
  apply Subtype.ext
  change (ell : A) ^ 3 = (ell : A) * (ell : A) * (ell : A)
  ring

private theorem literalLineCubic_fraction (b : Bool) (k : Fin 4) :
    Away.mk (grading L) (coordinate_mem L b) 3
      (standardTwistedCubicLiteralLineCubic (K := K) k : CoordinateRing L)
      (by simpa using (standardTwistedCubicLiteralLineCubic (K := K) k).property) =
      (if b then
        (![chartCoordinate L b false ^ 3, chartCoordinate L b false ^ 2,
          chartCoordinate L b false, 1] : Fin 4 → ChartRing L b) k
      else
        (![1, chartCoordinate L b true, chartCoordinate L b true ^ 2,
          chartCoordinate L b true ^ 3] : Fin 4 → ChartRing L b) k) := by
  let ell : grading L 1 := ⟨coordinate L b, coordinate_mem L b⟩
  let s : grading L 1 := ⟨coordinate L false, coordinate_mem L false⟩
  let t : grading L 1 := ⟨coordinate L true, coordinate_mem L true⟩
  have htuple : Away.mk (grading L) (coordinate_mem L b) 3
      (standardTwistedCubicLiteralLineCubic (K := K) k : CoordinateRing L)
      (by simpa using (standardTwistedCubicLiteralLineCubic (K := K) k).property) =
      (![chartCoordinate L b false ^ 3,
        chartCoordinate L b false ^ 2 * chartCoordinate L b true,
        chartCoordinate L b false * chartCoordinate L b true ^ 2,
        chartCoordinate L b true ^ 3] : Fin 4 → ChartRing L b) k := by
    fin_cases k
    · have h := nativeAway_threeProduct (grading L) ell s s s
        (standardTwistedCubicLiteralLineCubic (K := K) 0)
        (by simp only [literalLineCubic_raw]; simp <;> ring)
      simpa [chartCoordinate, AllCharacteristics.GradedChart.normalized,
        ell, s, ← pow_three'] using h
    · have h := nativeAway_threeProduct (grading L) ell s s t
        (standardTwistedCubicLiteralLineCubic (K := K) 1)
        (by simp only [literalLineCubic_raw]; simp <;> ring)
      simpa [chartCoordinate, AllCharacteristics.GradedChart.normalized,
        ell, s, t, pow_two] using h
    · have h := nativeAway_threeProduct (grading L) ell s t t
        (standardTwistedCubicLiteralLineCubic (K := K) 2)
        (by simp only [literalLineCubic_raw]; simp <;> ring)
      simpa [chartCoordinate, AllCharacteristics.GradedChart.normalized,
        ell, s, t, pow_two, mul_assoc] using h
    · have h := nativeAway_threeProduct (grading L) ell t t t
        (standardTwistedCubicLiteralLineCubic (K := K) 3)
        (by simp only [literalLineCubic_raw]; simp <;> ring)
      simpa [chartCoordinate, AllCharacteristics.GradedChart.normalized,
        ell, t, ← pow_three'] using h
  cases b <;> simpa only [Bool.false_eq_true, if_false, if_true,
    chartCoordinate_self, one_pow, one_mul, mul_one] using htuple

/-- Equality of the original chart-ring images, BEFORE structure-sheaf
and whole module morphisms are introduced. The literal fraction is unchanged. -/
private theorem originalChartCoefficient_literalFractionCut (b : Bool) (k : Fin 4) :
    (standardTwistedCubicNativeChartCoefficientMap (K := K) b)
      (chartCoordinate I (if b then 3 else 0) k) =
    Away.mk (grading L) (coordinate_mem L b) 3
      (standardTwistedCubicLiteralLineCubic (K := K) k : CoordinateRing L)
      (by simpa using (standardTwistedCubicLiteralLineCubic (K := K) k).property) := by
  cases b
  · exact (standardTwistedCubicChartZeroToLineChart_coordinate (K := K) k).trans
      (literalLineCubic_fraction (K := K) false k).symm
  · exact (standardTwistedCubicChartThreeToLineChart_coordinate (K := K) k).trans
      (literalLineCubic_fraction (K := K) true k).symm

/-- The original coefficient map gives EXACTLY the literal cubic's
degree-three away fraction, including both middle coordinates. -/
theorem standardTwistedCubicNativeChartMorphism_appTop_literalCubic
    (b : Bool) (k : Fin 4) :
    (standardTwistedCubicNativeChartMorphism (K := K) b).appTop.hom
      ((Scheme.ΓSpecIso (.of (ChartRing I (if b then 3 else 0)))).inv.hom
        (chartCoordinate I (if b then 3 else 0) k)) =
    (Scheme.ΓSpecIso (.of (ChartRing L b))).inv.hom
      (Away.mk (grading L) (coordinate_mem L b) 3
        (standardTwistedCubicLiteralLineCubic (K := K) k : CoordinateRing L)
        (by simpa using (standardTwistedCubicLiteralLineCubic (K := K) k).property)) := by
  have h := AllCharacteristics.specMap_appTop_globalSectionsIso_apply
    (standardTwistedCubicNativeChartCoefficientMap (K := K) b)
    (chartCoordinate I (if b then 3 else 0) k)
  exact h.trans (congrArg (Scheme.ΓSpecIso (.of (ChartRing L b))).inv.hom
    (originalChartCoefficient_literalFractionCut (K := K) b k))

private theorem literalLineDegreeOneGeneration :
    (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤
      Ideal.span (Set.range (fun f : grading L 1 => (f : CoordinateRing L))) :=
  gradedSurjective_irrelevant_le_span_degreeOne (homogeneousSubmodule Bool K) (grading L)
    (quotientGradedRingHom L) (quotientGradedRingHom_surjective L)
    mvPolynomial_irrelevant_le_span_degreeOne_small

/-- Canonical degree-one generation on an ABSTRACT original Bool quotient. -/
private theorem quotientLiteralDegreeOneGenerationCut
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) :
    (HomogeneousIdeal.irrelevant (grading J)).toIdeal ≤
      Ideal.span (Set.range (fun f : grading J 1 => (f : CoordinateRing J))) :=
  gradedSurjective_irrelevant_le_span_degreeOne (homogeneousSubmodule Bool K) (grading J)
    (quotientGradedRingHom J) (quotientGradedRingHom_surjective J)
    mvPolynomial_irrelevant_le_span_degreeOne_small

/-- The identical homogeneous cubic-section constructor, at abstract ideal level. -/
private def quotientLiteralSectionFactoryCut
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (q : grading J 3) :
    SheafOfModules.unit (scheme J).ringCatSheaf ⟶ positiveSheafOfModules (grading J) 3 :=
  (positiveSheafOfModules (grading J) 3).unitHomEquiv.symm
    (positiveGlobalSectionOfHomogeneous (grading J) 3 q)

/-- The identical canonical cubic-power frame, at abstract ideal level. -/
private def quotientLiteralNativePowerFrameFactoryCut
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b : Bool) :
    (Scheme.Modules.pullback (chartι J b)).obj (positiveSheafOfModules (grading J) 3) ≅
      SheafOfModules.unit (Spec (.of (ChartRing J b))).ringCatSheaf :=
  positiveThreePowerFrame_nativeChartUnitIso (grading J)
    ⟨coordinate J b, coordinate_mem J b⟩ (quotientLiteralDegreeOneGenerationCut J)

/-- Recover whole scalar action and cancel the inverse at ABSTRACT grading
level. No original curve, Bool quotient, literal cubic or native frame is substituted. -/
private theorem nativeHomogeneousCubicWholeActionCut
    {A ρ : Type u} [CommRing A] [SetLike ρ A] [AddSubgroupClass ρ A]
    (G : ℕ → ρ) [GradedRing G] (ell : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) (q : G 3) :
    (Scheme.Modules.pullback (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)).map
        ((positiveSheafOfModules G 3).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous G 3 q)) ≫
      (positiveThreePowerFrame_nativeChartUnitIso G ell hspan).hom =
    pullbackUnitComparison (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one) ≫
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (Away G (ell : A)))).inv.hom
          (Away.mk G ell.property 3 (q : A) (by simpa using q.property))) := by
  let c := pullbackUnitComparison (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)
  letI : IsIso c := isIso_pullbackUnitComparison
    (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)
  have h := positiveThreePowerFrame_nativeChart_homogeneousCoefficient G ell hspan q
  have he : inv c ≫
      ((Scheme.Modules.pullback (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)).map
        ((positiveSheafOfModules G 3).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous G 3 q)) ≫
        (positiveThreePowerFrame_nativeChartUnitIso G ell hspan).hom) =
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (Away G (ell : A)))).inv.hom
          (Away.mk G ell.property 3 (q : A) (by simpa using q.property))) :=
    (unitEndomorphismOfRegularFunction_value _).symm.trans
      (congrArg unitEndomorphismOfRegularFunction h)
  exact (IsIso.inv_comp_eq c).mp he

/-- Normalize only the original section-map/chart aliases, at abstract ideal level. -/
private theorem quotientLiteralNativeSectionMap_eq_rawCut
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b : Bool) (q : grading J 3) :
    (Scheme.Modules.pullback (chartι J b)).map (quotientLiteralSectionFactoryCut J q) =
    (Scheme.Modules.pullback (Proj.awayι (grading J) (coordinate J b)
      (coordinate_mem J b) Nat.zero_lt_one)).map
      ((positiveSheafOfModules (grading J) 3).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading J) 3 q)) := rfl

/-- Normalize only the native frame hom, at abstract ideal level. -/
private theorem quotientLiteralNativeFrameHom_eq_rawCut
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b : Bool) :
    (quotientLiteralNativePowerFrameFactoryCut J b).hom =
    (positiveThreePowerFrame_nativeChartUnitIso (grading J)
      ⟨coordinate J b, coordinate_mem J b⟩ (quotientLiteralDegreeOneGenerationCut J)).hom := rfl

private theorem quotientLiteralNativeLeft_eq_rawCut
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b : Bool) (q : grading J 3) :
    (Scheme.Modules.pullback (chartι J b)).map (quotientLiteralSectionFactoryCut J q) ≫
      (quotientLiteralNativePowerFrameFactoryCut J b).hom =
    (Scheme.Modules.pullback (Proj.awayι (grading J) (coordinate J b)
      (coordinate_mem J b) Nat.zero_lt_one)).map
      ((positiveSheafOfModules (grading J) 3).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading J) 3 q)) ≫
      (positiveThreePowerFrame_nativeChartUnitIso (grading J)
        ⟨coordinate J b, coordinate_mem J b⟩ (quotientLiteralDegreeOneGenerationCut J)).hom := by
  rw [quotientLiteralNativeSectionMap_eq_rawCut, quotientLiteralNativeFrameHom_eq_rawCut]

/-- Normalize the unit/scalar side independently of every positive module or frame. -/
private theorem quotientLiteralNativeRight_eq_rawCut
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b : Bool) (q : grading J 3) :
    pullbackUnitComparison (chartι J b) ≫ unitEndomorphismOfRegularFunction
      ((Scheme.ΓSpecIso (.of (ChartRing J b))).inv.hom
        (Away.mk (grading J) (coordinate_mem J b) 3 (q : CoordinateRing J)
          (by simpa using q.property))) =
    pullbackUnitComparison (Proj.awayι (grading J) (coordinate J b)
      (coordinate_mem J b) Nat.zero_lt_one) ≫ unitEndomorphismOfRegularFunction
      ((Scheme.ΓSpecIso (.of (Away (grading J) (coordinate J b)))).inv.hom
        (Away.mk (grading J) (coordinate_mem J b) 3 (q : CoordinateRing J)
          (by simpa using q.property))) := rfl

private theorem quotientLiteralNativeWholeActionCut
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b : Bool) (q : grading J 3) :
    (Scheme.Modules.pullback (chartι J b)).map (quotientLiteralSectionFactoryCut J q) ≫
      (quotientLiteralNativePowerFrameFactoryCut J b).hom =
    pullbackUnitComparison (chartι J b) ≫ unitEndomorphismOfRegularFunction
      ((Scheme.ΓSpecIso (.of (ChartRing J b))).inv.hom
        (Away.mk (grading J) (coordinate_mem J b) 3 (q : CoordinateRing J)
          (by simpa using q.property))) := by
  calc
    _ = _ := quotientLiteralNativeLeft_eq_rawCut J b q
    _ = _ := nativeHomogeneousCubicWholeActionCut (grading J)
      ⟨coordinate J b, coordinate_mem J b⟩ (quotientLiteralDegreeOneGenerationCut J) q
    _ = _ := (quotientLiteralNativeRight_eq_rawCut J b q).symm

/-- The original native power-frame Iso is identical to the abstract factory.
Only proof-irrelevant degree-one generation witnesses differ. -/
private theorem originalPowerNativeFrame_iso_eq_factoryCut (b : Bool) :
    standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b =
      quotientLiteralNativePowerFrameFactoryCut L b := rfl

private theorem originalPowerNativeFrameHom_eq_factoryCut (b : Bool) :
    (standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b).hom =
      (quotientLiteralNativePowerFrameFactoryCut L b).hom :=
  congrArg (fun e => e.hom) (originalPowerNativeFrame_iso_eq_factoryCut (K := K) b)

/-- The original literal whole section-map is unchanged; only a factory alias is exposed. -/
private theorem originalLiteralSectionNativeMap_eq_factoryCut (b : Bool) (k : Fin 4) :
    (Scheme.Modules.pullback (chartι L b)).map
      (standardTwistedCubicLiteralLineSectionHom (K := K) k) =
    (Scheme.Modules.pullback (chartι L b)).map
      (quotientLiteralSectionFactoryCut L (standardTwistedCubicLiteralLineCubic (K := K) k)) := rfl

private theorem categoricalComp_congrCut
    {D : Type*} [Category D] {P Q R : D}
    {f f' : P ⟶ Q} {g g' : Q ⟶ R} (hf : f = f') (hg : g = g') :
    f ≫ g = f' ≫ g' := congrArg₂ (fun a b => a ≫ b) hf hg

private theorem literalNativeScalar_congrCut {X : Scheme.{u}}
    {P : X.Modules} (c : P ⟶ SheafOfModules.unit X.ringCatSheaf)
    {r t : Γ(X, ⊤)} (h : r = t) :
    c ≫ unitEndomorphismOfRegularFunction r = c ≫ unitEndomorphismOfRegularFunction t :=
  congrArg (fun z => c ≫ unitEndomorphismOfRegularFunction z) h

private theorem literalLineSection_nativeChart_action (b : Bool) (k : Fin 4) :
    (Scheme.Modules.pullback (chartι L b)).map
        (standardTwistedCubicLiteralLineSectionHom (K := K) k) ≫
      (standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b).hom =
    pullbackUnitComparison (chartι L b) ≫ unitEndomorphismOfRegularFunction
      ((Scheme.ΓSpecIso (.of (ChartRing L b))).inv.hom
        (Away.mk (grading L) (coordinate_mem L b) 3
          (standardTwistedCubicLiteralLineCubic (K := K) k : CoordinateRing L)
          (by simpa using (standardTwistedCubicLiteralLineCubic (K := K) k).property))) := by
  exact (categoricalComp_congrCut
    (originalLiteralSectionNativeMap_eq_factoryCut (K := K) b k)
    (originalPowerNativeFrameHom_eq_factoryCut (K := K) b)).trans
      (quotientLiteralNativeWholeActionCut L b
        (standardTwistedCubicLiteralLineCubic (K := K) k))

/-- The original basis-comparison hom constructor, projected separately
from every literal all-coordinate equality. -/
private theorem originalPowerBasisIso_hom_decomposeCut (b : Bool) :
    (standardTwistedCubicOriginalPowerBasisOverIso (K := K) b).hom =
    CategoryTheory.inv («I» := standardTwistedCubicPulledCoordinate_originalOpen_isIso (K := K) b)
      ((standardTwistedCubicPulledCoordinateHom (K := K) (if b then 3 else 0)).over
        (quotientCoordinateOpen L b)) ≫
    (positiveThreePowerFrameHom (grading L) ⟨coordinate L b, coordinate_mem L b⟩).over
      (quotientCoordinateOpen L b) := by
  letI : IsIso ((standardTwistedCubicPulledCoordinateHom (K := K)
      (if b then 3 else 0)).over (quotientCoordinateOpen L b)) :=
    standardTwistedCubicPulledCoordinate_originalOpen_isIso (K := K) b
  letI : IsIso ((positiveThreePowerFrameHom (grading L)
      ⟨coordinate L b, coordinate_mem L b⟩).over (quotientCoordinateOpen L b)) :=
    standardProjectiveLine_originalPowerFrame_over_isIso (K := K) b
  rfl

/-- The SAME original local basis comparison sends EVERY original
pulled coordinate to its literal parametrizing native cubic-section map. -/
theorem standardTwistedCubicOriginalPowerBasisOverIso_coordinate (b : Bool) (k : Fin 4) :
    (standardTwistedCubicPulledCoordinateHom (K := K) k).over (quotientCoordinateOpen L b) ≫
      (standardTwistedCubicOriginalPowerBasisOverIso (K := K) b).hom =
    (standardTwistedCubicLiteralLineSectionHom (K := K) k).over
      (quotientCoordinateOpen L b) := by
  let U := quotientCoordinateOpen L b
  let j := chartι L b
  let E := nativeOriginalChartOverModuleEquivalence j U (chartι_opensRange L b)
  let n := nativeOriginalChartOverPullbackComparison j U (chartι_opensRange L b)
  let eM := n.app M ≪≫ standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b
  let eN := n.app N ≪≫ standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b
  let w := nativeOriginalChartOverUnitIso j U (chartι_opensRange L b)
  let s₀ := standardTwistedCubicPulledCoordinateHom (K := K) (if b then 3 else 0)
  let s₁ := standardTwistedCubicPulledCoordinateHom (K := K) k
  let t₀ := positiveThreePowerFrameHom (grading L) ⟨coordinate L b, coordinate_mem L b⟩
  let t₁ := standardTwistedCubicLiteralLineSectionHom (K := K) k
  let q := unitEndomorphismOfRegularFunction
    ((Scheme.ΓSpecIso (.of (ChartRing L b))).inv.hom
      (Away.mk (grading L) (coordinate_mem L b) 3
        (standardTwistedCubicLiteralLineCubic (K := K) k : CoordinateRing L)
        (by simpa using (standardTwistedCubicLiteralLineCubic (K := K) k).property)))
  let hs₀Iso := standardTwistedCubicPulledCoordinate_originalOpen_isIso (K := K) b
  let ht₀Iso := standardProjectiveLine_originalPowerFrame_over_isIso (K := K) b
  letI : IsIso (s₀.over U) := hs₀Iso
  letI : IsIso (t₀.over U) := ht₀Iso
  have hs : (Scheme.Modules.pullback j).map s₁ ≫
      (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b).hom =
      pullbackUnitComparison j ≫ q := by
    exact (standardTwistedCubicPulledCoordinate_nativeChart_action (K := K) b k).trans
      (literalNativeScalar_congrCut (pullbackUnitComparison j)
        (standardTwistedCubicNativeChartMorphism_appTop_literalCubic (K := K) b k))
  have h := @nativeOriginalBasisTransitions_eq_of_chartActions _ _ _ _ E _ _ _ _
    (s₀.over U) (s₁.over U) (t₀.over U) (t₁.over U) hs₀Iso ht₀Iso eM eN w q
    (nativeOriginalChartFramedBasisAction j U (chartι_opensRange L b) M s₀
      (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b)
      (standardTwistedCubicPulledCoordinate_nativeChart_basis b))
    (nativeOriginalChartFramedScalarAction j U (chartι_opensRange L b) M s₁
      (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b) q hs)
    (nativeOriginalChartFramedBasisAction j U (chartι_opensRange L b) N t₀
      (standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b)
      (standardProjectiveLineOriginalPower_nativeChart_basis b))
    (nativeOriginalChartFramedScalarAction j U (chartι_opensRange L b) N t₁
      (standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b) q
      (literalLineSection_nativeChart_action b k))
  have hraw := @nativeOriginalOtherBasis_comp_comparison _ _ _ _ _
    (s₀.over U) (s₁.over U) (t₀.over U) (t₁.over U) hs₀Iso ht₀Iso h
  exact (congrArg (fun e => s₁.over U ≫ e)
    (originalPowerBasisIso_hom_decomposeCut (K := K) b)).trans hraw

/-- Restriction of the SAME glued Iso hom, normalized while modules and
all local Isos remain abstract. -/
private theorem nativeActualGlueIsoHom_overCut
    {X : Scheme.{u}} (P Q : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (e : ∀ i, P.over (U i) ≅ Q.over (U i))
    (hcompat : ∀ i j,
      (SchemeModuleInternalHom.sheaf P Q).val.map
        (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
        ((sectionsEquivOver P Q (U i)).symm (e i).hom) =
      (SchemeModuleInternalHom.sheaf P Q).val.map
        (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
        ((sectionsEquivOver P Q (U j)).symm (e j).hom)) (i : ι) :
    (schemeModuleIsoGlueOfActualCompatibleOverIsos P Q U hcover e hcompat).hom.over
      (U i) = (e i).hom := by
  change (schemeModuleHomGlueOfActualCompatibleOverMorphisms P Q U hcover
    (fun i => (e i).hom) hcompat).over (U i) = (e i).hom
  exact schemeModuleHomGlueOfActualCompatibleOverMorphisms_over P Q U hcover
    (fun i => (e i).hom) hcompat i

private theorem nativeActualModuleComp_overCut
    {X : Scheme.{u}} {P Q R : X.Modules} (f : P ⟶ Q) (g : Q ⟶ R) (U : X.Opens) :
    (f ≫ g).over U = f.over U ≫ g.over U := rfl

/-- Whole-map equality from equality on the SAME covering opens, before
original positive modules or literal cubic sections are substituted. -/
private theorem nativeActualWholeMap_eq_of_overCoverCut
    {X : Scheme.{u}} (P Q : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤) (f g : P ⟶ Q)
    (hlocal : ∀ i, f.over (U i) = g.over (U i)) : f = g := by
  apply (schemeModuleActualInternalHomTopEquiv P Q).symm.injective
  change homSection f ⊤ = homSection g ⊤
  apply schemeModuleSections_ext (SchemeModuleInternalHom.sheaf P Q) ⊤
    U (fun _ => le_top) hcover.ge
  intro i
  rw [homSection_restrict, homSection_restrict]
  exact congrArg (sectionsEquivOver P Q (U i)).symm (hlocal i)

private theorem standardNativePositiveOnePullbackIso_over (b : Bool) :
    (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom.over
      (quotientCoordinateOpen L b) =
    (standardTwistedCubicOriginalPowerBasisOverIso (K := K) b).hom := by
  exact nativeActualGlueIsoHom_overCut M N
    (fun b : ULift.{u} Bool => quotientCoordinateOpen L b.down)
    (standardProjectiveLineOriginalPowerOpen_cover (K := K))
    (fun b => standardTwistedCubicOriginalPowerBasisOverIso (K := K) b.down)
    (fun b c => standardTwistedCubicOriginalPowerBasisOverIso_compatible b.down c.down) ⟨b⟩

/-- Literal ALL-FOUR global image assertion, as equality of whole original
module-sheaf morphisms under the SAME genuine global native Iso. -/
theorem standardTwistedCubicNativePositiveOnePullbackIso_coordinate (k : Fin 4) :
    standardTwistedCubicPulledCoordinateHom (K := K) k ≫
      (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom =
    standardTwistedCubicLiteralLineSectionHom (K := K) k := by
  apply nativeActualWholeMap_eq_of_overCoverCut
    (SheafOfModules.unit (scheme L).ringCatSheaf) N
    (fun b : ULift.{u} Bool => quotientCoordinateOpen L b.down)
    (standardProjectiveLineOriginalPowerOpen_cover (K := K))
  intro b
  exact (nativeActualModuleComp_overCut
    (standardTwistedCubicPulledCoordinateHom (K := K) k)
    (standardTwistedCubicNativePositiveOnePullbackIso (K := K)).hom
    (quotientCoordinateOpen L b.down)).trans
      ((congrArg (fun e =>
        (standardTwistedCubicPulledCoordinateHom (K := K) k).over
          (quotientCoordinateOpen L b.down) ≫ e)
        (standardNativePositiveOnePullbackIso_over (K := K) b.down)).trans
        (standardTwistedCubicOriginalPowerBasisOverIso_coordinate (K := K) b.down k))

end PfaffianDescent.QuarticNet

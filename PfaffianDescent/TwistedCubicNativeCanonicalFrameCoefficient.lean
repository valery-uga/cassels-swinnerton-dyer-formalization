import PfaffianDescent.NativeOpenPullbackFramedSection
import PfaffianDescent.TwistedCubicNativePositivePullbackCharts
import PfaffianDescent.ActualPositiveTwistRefinedUnitCoefficient
import PfaffianDescent.NativeRefinedPullbackFramedCoefficient
import PfaffianDescent.PositiveThreeNativeRefinedCoefficient

/-! SOURCE ONLY. Original actual O(1) homogeneous sections, canonical actual
Spec-chart frames and their WHOLE native unit scalar action. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Bounded coefficient transport BEFORE substituting the original twisted
cubic ideal. The SAME actual chart basis, original basicOpenIsoSpec and native
pullback/restriction maps are retained throughout. -/
private theorem actualPositiveOneNativeRefinedCoefficientCut
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell eta : grading J 1) :
    let U := Proj.basicOpen (grading J) (ell : CoordinateRing J)
    let e := Proj.basicOpenIsoSpec (grading J) (ell : CoordinateRing J)
      ell.property Nat.zero_lt_one
    let T := positiveSheafOfModules (grading J) 1
    let j := Proj.awayι (grading J) (ell : CoordinateRing J) ell.property Nat.zero_lt_one
    unitEndomorphismValue
      (CategoryTheory.inv («I» := isIso_pullbackUnitComparison j)
        (pullbackUnitComparison j) ≫
        (Scheme.Modules.pullback j).map
          (T.unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading J) 1 eta)) ≫
        ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app T ≪≫
          cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv T
            (actualPositiveTwistChartUnitIso J ell 1)).hom) =
    (Scheme.ΓSpecIso (.of (Away (grading J) (ell : CoordinateRing J)))).inv.hom
      (Away.mk (grading J) ell.property 1 (eta : CoordinateRing J)
        (by simpa using eta.property)) := by
  dsimp only
  let U := Proj.basicOpen (grading J) (ell : CoordinateRing J)
  let e := Proj.basicOpenIsoSpec (grading J) (ell : CoordinateRing J)
    ell.property Nat.zero_lt_one
  let T := positiveSheafOfModules (grading J) 1
  let p := actualPositiveTwistChartUnitIso J ell 1
  let s := T.unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading J) 1 eta)
  have h := nativeRefinedPullbackFramedCoefficient U e.inv T p s
  have hOld := actualPositiveTwistChartUnitHomogeneousCoefficient J ell 1 eta
  have hTransport := congrArg (fun z => e.inv.appTop z) hOld
  exact h.trans (hTransport.trans
    (nativeBasicOpenIsoSpec_inv_appTop_awaySection (grading J) ell _))

local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "T" => positiveSheafOfModules (grading I) 1

/-- The IDENTICAL original coordinate-section constructor, behind an
abstract homogeneous-ideal factory before the twisted cubic is substituted. -/
private def actualPositiveOneCoordinateHomFactory
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (k : Fin 4) :
    SheafOfModules.unit (scheme J).ringCatSheaf ⟶ positiveSheafOfModules (grading J) 1 :=
  (positiveSheafOfModules (grading J) 1).unitHomEquiv.symm
    (positiveGlobalSectionOfHomogeneous (grading J) 1
      ⟨coordinate J k, coordinate_mem J k⟩)

/-- The IDENTICAL original refined frame, with the actual original
chartι/ChartRing header and an abstract ideal index. -/
private def actualPositiveOneCanonicalNativeChartFactory
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (k : Fin 4) :
    (Scheme.Modules.pullback (chartι J k)).obj (positiveSheafOfModules (grading J) 1) ≅
      SheafOfModules.unit (Spec (.of (ChartRing J k))).ringCatSheaf := by
  let ell : grading J 1 := ⟨coordinate J k, coordinate_mem J k⟩
  let U := Proj.basicOpen (grading J) (coordinate J k)
  let e := Proj.basicOpenIsoSpec (grading J) (coordinate J k)
    (coordinate_mem J k) Nat.zero_lt_one
  let Q := positiveSheafOfModules (grading J) 1
  let eR := cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso
    U e.inv Q (actualPositiveTwistChartUnitIso J ell 1)
  exact (Scheme.Modules.restrictFunctorIsoPullback (chartι J k)).symm.app Q ≪≫ eR

/-- Isolate only the original coordinate-section constructor. -/
private theorem actualPositiveOneCoordinateFactory_eq_literal
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (k : Fin 4) :
    actualPositiveOneCoordinateHomFactory J k = ((positiveSheafOfModules (grading J) 1).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous (grading J) 1
            ⟨coordinate J k, coordinate_mem J k⟩)) := rfl

/-- Isolate only the pullback-map alias, with the same literal section. -/
private theorem actualPositiveOneNativeSectionMap_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j k : Fin 4) :
    (Scheme.Modules.pullback (chartι J j)).map (actualPositiveOneCoordinateHomFactory J k) =
      (Scheme.Modules.pullback (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)).map ((positiveSheafOfModules (grading J) 1).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous (grading J) 1
            ⟨coordinate J k, coordinate_mem J k⟩)) := by
  rw [actualPositiveOneCoordinateFactory_eq_literal]
  rfl

/-- Dependent comparison transport proved BEFORE any chart, graded ring
or positive module is substituted; equal open maps give the same component. -/
private theorem nativeRestrictPullbackComparisonHom_heq_of_eq
    {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (hf : IsOpenImmersion f) (hg : IsOpenImmersion g) (h : f = g) (Q : Y.Modules) :
    letI : IsOpenImmersion f := hf
    letI : IsOpenImmersion g := hg
    HEq ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app Q)
      ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app Q) := by
  cases h
  rfl

/-- Equality transport of the WHOLE native Iso, before any graded scheme
or module is substituted. Projection to its Hom is a separate operation. -/
private theorem nativeRestrictPullbackComparisonIso_heq_of_eq
    {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (hf : IsOpenImmersion f) (hg : IsOpenImmersion g) (h : f = g) (Q : Y.Modules) :
    letI : IsOpenImmersion f := hf
    letI : IsOpenImmersion g := hg
    HEq ((Scheme.Modules.restrictFunctorIsoPullback f).symm.app Q)
      ((Scheme.Modules.restrictFunctorIsoPullback g).symm.app Q) := by
  cases h
  rfl

/-- Original chart normalization at Iso level. The coefficient module is
an arbitrary native module, and neither Iso hom is projected here. -/
private theorem actualPositiveOneRestrictionComparisonIso_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (Q : (scheme J).Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback (chartι J j)).symm.app Q =
      (Scheme.Modules.restrictFunctorIsoPullback
        (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j)
          Nat.zero_lt_one)).symm.app Q := by
  have hmap : chartι J j =
      Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one := rfl
  exact eq_of_heq (nativeRestrictPullbackComparisonIso_heq_of_eq (chartι J j)
    (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)
    (by infer_instance) (by infer_instance) hmap Q)

/-- Only the restriction-to-pullback Iso component is transported. The
module stays ABSTRACT, so no positive-twist/refined-frame chain is reduced. -/
private theorem actualPositiveOneRestrictionComparisonHom_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4)
    (Q : (scheme J).Modules) :
    ((Scheme.Modules.restrictFunctorIsoPullback (chartι J j)).symm.app Q).hom =
    ((Scheme.Modules.restrictFunctorIsoPullback
      (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)).symm.app Q).hom := by
  exact congrArg (fun a => a.hom)
    (actualPositiveOneRestrictionComparisonIso_eq_raw J j Q)

/-- Normalize only the Iso constructor itself. The identical original
chart alias is retained on both sides; no dependent Hom is projected. -/
private theorem actualPositiveOneNativeFrameFactory_iso_decompose
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    actualPositiveOneCanonicalNativeChartFactory J j =
      (Scheme.Modules.restrictFunctorIsoPullback (chartι J j)).symm.app
        (positiveSheafOfModules (grading J) 1) ≪≫
      (let U := Proj.basicOpen (grading J) (coordinate J j)
       let e := Proj.basicOpenIsoSpec (grading J) (coordinate J j)
         (coordinate_mem J j) Nat.zero_lt_one
       let Q := positiveSheafOfModules (grading J) 1
       cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv Q
         (actualPositiveTwistChartUnitIso J ⟨coordinate J j, coordinate_mem J j⟩ 1)) := rfl

/-- Expose only the TWO original Iso components of the original factory,
retaining its original chart comparison and refined component separately. -/
private theorem actualPositiveOneNativeFrameFactory_hom_decompose
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    (actualPositiveOneCanonicalNativeChartFactory J j).hom =
      ((Scheme.Modules.restrictFunctorIsoPullback (chartι J j)).symm.app
      (positiveSheafOfModules (grading J) 1)).hom ≫ (let U := Proj.basicOpen (grading J) (coordinate J j)
     let e := Proj.basicOpenIsoSpec (grading J) (coordinate J j)
       (coordinate_mem J j) Nat.zero_lt_one
     let Q := positiveSheafOfModules (grading J) 1
     cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv Q
       (actualPositiveTwistChartUnitIso J ⟨coordinate J j, coordinate_mem J j⟩ 1)).hom := by
  have h := congrArg (fun a => a.hom)
    (actualPositiveOneNativeFrameFactory_iso_decompose J j)
  exact h.trans (Iso.trans_hom _ _)


/-- Expose only the two RAW Iso components; their scalar/refinement
definitions are not normalized against original chart aliases here. -/
private theorem actualPositiveOneRawNativeFrame_hom_decompose
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    (let U := Proj.basicOpen (grading J) (coordinate J j)
       let e := Proj.basicOpenIsoSpec (grading J) (coordinate J j)
         (coordinate_mem J j) Nat.zero_lt_one
       let Q := positiveSheafOfModules (grading J) 1
       (Scheme.Modules.restrictFunctorIsoPullback
         (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)).symm.app Q ≪≫
         cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv Q
           (actualPositiveTwistChartUnitIso J ⟨coordinate J j, coordinate_mem J j⟩ 1)).hom = ((Scheme.Modules.restrictFunctorIsoPullback
      (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)).symm.app
        (positiveSheafOfModules (grading J) 1)).hom ≫ (let U := Proj.basicOpen (grading J) (coordinate J j)
     let e := Proj.basicOpenIsoSpec (grading J) (coordinate J j)
       (coordinate_mem J j) Nat.zero_lt_one
     let Q := positiveSheafOfModules (grading J) 1
     cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv Q
       (actualPositiveTwistChartUnitIso J ⟨coordinate J j, coordinate_mem J j⟩ 1)).hom := by
  dsimp only
  exact Iso.trans_hom _ _

/-- Isolate only the native-frame Hom constructor, without coefficient evaluation. -/
private theorem actualPositiveOneNativeFrameHom_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    (actualPositiveOneCanonicalNativeChartFactory J j).hom = (let U := Proj.basicOpen (grading J) (coordinate J j)
       let e := Proj.basicOpenIsoSpec (grading J) (coordinate J j)
         (coordinate_mem J j) Nat.zero_lt_one
       let Q := positiveSheafOfModules (grading J) 1
       (Scheme.Modules.restrictFunctorIsoPullback
         (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)).symm.app Q ≪≫
         cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv Q
           (actualPositiveTwistChartUnitIso J ⟨coordinate J j, coordinate_mem J j⟩ 1)).hom  := by
  rw [actualPositiveOneNativeFrameFactory_hom_decompose]
  have h := actualPositiveOneRestrictionComparisonHom_eq_raw J j
    (positiveSheafOfModules (grading J) 1)
  have hc := congrArg (fun a => a ≫ (let U := Proj.basicOpen (grading J) (coordinate J j)
     let e := Proj.basicOpenIsoSpec (grading J) (coordinate J j)
       (coordinate_mem J j) Nat.zero_lt_one
     let Q := positiveSheafOfModules (grading J) 1
     cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv Q
       (actualPositiveTwistChartUnitIso J ⟨coordinate J j, coordinate_mem J j⟩ 1)).hom) h
  exact hc.trans (actualPositiveOneRawNativeFrame_hom_decompose J j).symm

/-- Isolate only the canonical unit inverse and its raw chart alias. -/
private theorem actualPositiveOneNativeUnitInverse_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j : Fin 4) :
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison (chartι J j))
        (pullbackUnitComparison (chartι J j)) = CategoryTheory.inv («I» := isIso_pullbackUnitComparison
        (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one))
      (pullbackUnitComparison
        (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)) := rfl

/-- Combine the three independent entire-map transports. No Gamma/ratio
or homogeneous coefficient theorem is unfolded in this declaration. -/
private theorem actualPositiveOneNativeLeftChain_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j k : Fin 4) :
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison (chartι J j))
        (pullbackUnitComparison (chartι J j)) ≫
        (Scheme.Modules.pullback (chartι J j)).map (actualPositiveOneCoordinateHomFactory J k) ≫
        (actualPositiveOneCanonicalNativeChartFactory J j).hom = CategoryTheory.inv («I» := isIso_pullbackUnitComparison
        (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one))
      (pullbackUnitComparison
        (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)) ≫
      (Scheme.Modules.pullback (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)).map ((positiveSheafOfModules (grading J) 1).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous (grading J) 1
            ⟨coordinate J k, coordinate_mem J k⟩)) ≫
      (let U := Proj.basicOpen (grading J) (coordinate J j)
       let e := Proj.basicOpenIsoSpec (grading J) (coordinate J j)
         (coordinate_mem J j) Nat.zero_lt_one
       let Q := positiveSheafOfModules (grading J) 1
       (Scheme.Modules.restrictFunctorIsoPullback
         (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)).symm.app Q ≪≫
         cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv Q
           (actualPositiveTwistChartUnitIso J ⟨coordinate J j, coordinate_mem J j⟩ 1)).hom := by
  rw [actualPositiveOneNativeUnitInverse_eq_raw,
    actualPositiveOneNativeSectionMap_eq_raw, actualPositiveOneNativeFrameHom_eq_raw]

/-- The scalar/Gamma/fraction normalization is independent of every
positive module, coordinate-section map and native frame constructor. -/
private theorem actualPositiveOneNativeScalar_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j k : Fin 4) :
    (Scheme.ΓSpecIso (.of (ChartRing J j))).inv.hom (chartCoordinate J j k) = (Scheme.ΓSpecIso (.of (Away (grading J) (coordinate J j)))).inv.hom
      (Away.mk (grading J) (coordinate_mem J j) 1 (coordinate J k)
        (by simpa using coordinate_mem J k)) := rfl

/-- Perform all chart/factory alias conversion at the ABSTRACT ideal level. -/
private theorem actualPositiveOneCanonicalNativeChartFactory_coefficient
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (j k : Fin 4) :
    unitEndomorphismValue
      (CategoryTheory.inv («I» := isIso_pullbackUnitComparison (chartι J j))
        (pullbackUnitComparison (chartι J j)) ≫
        (Scheme.Modules.pullback (chartι J j)).map (actualPositiveOneCoordinateHomFactory J k) ≫
        (actualPositiveOneCanonicalNativeChartFactory J j).hom) =
    (Scheme.ΓSpecIso (.of (ChartRing J j))).inv.hom (chartCoordinate J j k) := by
  calc
    _ = unitEndomorphismValue
      (CategoryTheory.inv («I» := isIso_pullbackUnitComparison
        (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one))
      (pullbackUnitComparison
        (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)) ≫
      (Scheme.Modules.pullback (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)).map ((positiveSheafOfModules (grading J) 1).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous (grading J) 1
            ⟨coordinate J k, coordinate_mem J k⟩)) ≫
      (let U := Proj.basicOpen (grading J) (coordinate J j)
       let e := Proj.basicOpenIsoSpec (grading J) (coordinate J j)
         (coordinate_mem J j) Nat.zero_lt_one
       let Q := positiveSheafOfModules (grading J) 1
       (Scheme.Modules.restrictFunctorIsoPullback
         (Proj.awayι (grading J) (coordinate J j) (coordinate_mem J j) Nat.zero_lt_one)).symm.app Q ≪≫
         cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv Q
           (actualPositiveTwistChartUnitIso J ⟨coordinate J j, coordinate_mem J j⟩ 1)).hom) := congrArg unitEndomorphismValue
        (actualPositiveOneNativeLeftChain_eq_raw J j k)
    _ = (Scheme.ΓSpecIso (.of (Away (grading J) (coordinate J j)))).inv.hom
      (Away.mk (grading J) (coordinate_mem J j) 1 (coordinate J k)
        (by simpa using coordinate_mem J k)) := actualPositiveOneNativeRefinedCoefficientCut J
      ⟨coordinate J j, coordinate_mem J j⟩
      ⟨coordinate J k, coordinate_mem J k⟩
    _ = _ := (actualPositiveOneNativeScalar_eq_raw J j k).symm

/-- The actual global coordinate-section map, retaining its original
homogeneous positive-sheaf constructor. -/
def standardTwistedCubicPositiveOneCoordinateHom (j : Fin 4) :
    SheafOfModules.unit (scheme I).ringCatSheaf ⟶ T :=
  actualPositiveOneCoordinateHomFactory I j

/-- Canonical actual refined frame, constructed from the ORIGINAL unit Iso
and original basicOpenIsoSpec; no frame/action certificate is supplied. -/
def standardTwistedCubicPositiveOne_canonicalNativeChartUnitIso (j : Fin 4) :
    (Scheme.Modules.pullback (chartι I j)).obj T ≅
      SheafOfModules.unit (Spec (.of (ChartRing I j))).ringCatSheaf :=
  actualPositiveOneCanonicalNativeChartFactory I j

/-- Definitionally SAME original coordinate map, without any new choice. -/
private theorem standardPositiveOneCoordinate_factory_preserves (k : Fin 4) :
    standardTwistedCubicPositiveOneCoordinateHom (K := K) k =
      (positiveSheafOfModules (grading I) 1).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) 1
          ⟨coordinate I k, coordinate_mem I k⟩) := rfl

/-- Definitionally SAME original native frame; the full former constructor
is retained, with only proof-irrelevant positivity witnesses normalized. -/
private theorem standardPositiveOneNativeFrame_factory_preserves (j : Fin 4) :
    standardTwistedCubicPositiveOne_canonicalNativeChartUnitIso (K := K) j =
      (let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
       let U := Proj.basicOpen (grading I) (coordinate I j)
       let e := Proj.basicOpenIsoSpec (grading I) (coordinate I j)
         (coordinate_mem I j) (by decide : 0 < 1)
       let eR := cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso
         U e.inv T (actualPositiveTwistChartUnitIso I ell 1)
       (Scheme.Modules.restrictFunctorIsoPullback (chartι I j)).symm.app T ≪≫ eR) := rfl

/-- RAW original graded-away specialization, before expanding any named
original coordinate-section or canonical native-frame definition. -/
private theorem originalRawPositiveOneNativeRefinedCoefficient (a b : Fin 4) :
    let U := Proj.basicOpen (grading I) (coordinate I a)
    let e := Proj.basicOpenIsoSpec (grading I) (coordinate I a)
      (coordinate_mem I a) Nat.zero_lt_one
    let T₀ := positiveSheafOfModules (grading I) 1
    let j := Proj.awayι (grading I) (coordinate I a)
      (coordinate_mem I a) Nat.zero_lt_one
    unitEndomorphismValue
      (CategoryTheory.inv («I» := isIso_pullbackUnitComparison j)
        (pullbackUnitComparison j) ≫
        (Scheme.Modules.pullback j).map
          (T₀.unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading I) 1
            ⟨coordinate I b, coordinate_mem I b⟩)) ≫
        ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app T₀ ≪≫
          cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv T₀
            (actualPositiveTwistChartUnitIso I
              ⟨coordinate I a, coordinate_mem I a⟩ 1)).hom) =
    (Scheme.ΓSpecIso (.of (Away (grading I) (coordinate I a)))).inv.hom
      (Away.mk (grading I) (coordinate_mem I a) 1 (coordinate I b)
        (by simpa using coordinate_mem I b)) :=
  actualPositiveOneNativeRefinedCoefficientCut I
    ⟨coordinate I a, coordinate_mem I a⟩
    ⟨coordinate I b, coordinate_mem I b⟩

/-- Only the elementary raw fraction is identified with its SAME original
chart coordinate, independently of any module-sheaf or pullback definition. -/
private theorem originalRawPositiveOneNativeCoordinate (a b : Fin 4) :
    Away.mk (grading I) (coordinate_mem I a) 1 (coordinate I b)
      (by simpa using coordinate_mem I b) = chartCoordinate I a b := rfl

/-- Literal native coefficient of ANY original homogeneous coordinate
section in this SAME canonical chart frame. -/
theorem standardTwistedCubicPositiveOne_canonicalNativeChart_coefficient
    (j k : Fin 4) :
    unitEndomorphismValue
      (CategoryTheory.inv («I» := isIso_pullbackUnitComparison (chartι I j))
        (pullbackUnitComparison (chartι I j)) ≫
        (Scheme.Modules.pullback (chartι I j)).map
          (standardTwistedCubicPositiveOneCoordinateHom (K := K) k) ≫
        (standardTwistedCubicPositiveOne_canonicalNativeChartUnitIso (K := K) j).hom) =
    (Scheme.ΓSpecIso (.of (ChartRing I j))).inv.hom (chartCoordinate I j k) := by
  exact actualPositiveOneCanonicalNativeChartFactory_coefficient I j k

/-- WHOLE actual unit-endomorphism action, not merely a coefficient or
pointwise dimension equality. -/
theorem standardTwistedCubicPositiveOne_canonicalNativeChart_unitScalar
    (j k : Fin 4) :
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison (chartι I j))
        (pullbackUnitComparison (chartι I j)) ≫
        (Scheme.Modules.pullback (chartι I j)).map
          (standardTwistedCubicPositiveOneCoordinateHom (K := K) k) ≫
        (standardTwistedCubicPositiveOne_canonicalNativeChartUnitIso (K := K) j).hom =
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (ChartRing I j))).inv.hom (chartCoordinate I j k)) := by
  calc
    _ = unitEndomorphismOfRegularFunction (unitEndomorphismValue
        (CategoryTheory.inv («I» := isIso_pullbackUnitComparison (chartι I j))
        (pullbackUnitComparison (chartι I j)) ≫
          (Scheme.Modules.pullback (chartι I j)).map
            (standardTwistedCubicPositiveOneCoordinateHom (K := K) k) ≫
          (standardTwistedCubicPositiveOne_canonicalNativeChartUnitIso (K := K) j).hom)) :=
      (unitEndomorphismOfRegularFunction_value _).symm
    _ = _ := congrArg unitEndomorphismOfRegularFunction
      (standardTwistedCubicPositiveOne_canonicalNativeChart_coefficient j k)

/-- The selected ORIGINAL homogeneous coordinate section is an actual
basis in this chart, internally derived from its exact native coefficient. -/
theorem standardTwistedCubicPositiveOne_canonicalNativeChart_basis
    (j : Fin 4) :
    (Scheme.Modules.pullback (chartι I j)).map
        (standardTwistedCubicPositiveOneCoordinateHom (K := K) j) ≫
      (standardTwistedCubicPositiveOne_canonicalNativeChartUnitIso (K := K) j).hom =
    pullbackUnitComparison (chartι I j) := by
  have h := standardTwistedCubicPositiveOne_canonicalNativeChart_unitScalar (K := K) j j
  rw [chartCoordinate_self, map_one, unitEndomorphismOfRegularFunction_one] at h
  let c := pullbackUnitComparison (chartι I j)
  letI : IsIso c := isIso_pullbackUnitComparison (chartι I j)
  have h' : inv c ≫
      ((Scheme.Modules.pullback (chartι I j)).map
        (standardTwistedCubicPositiveOneCoordinateHom (K := K) j) ≫
        (standardTwistedCubicPositiveOne_canonicalNativeChartUnitIso (K := K) j).hom) =
      𝟙 _ := h
  simpa only [Category.comp_id] using (IsIso.inv_comp_eq c).mp h'

end PfaffianDescent.QuarticNet

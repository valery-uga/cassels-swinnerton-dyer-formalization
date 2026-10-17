import PfaffianDescent.ProjectivePositiveHomogeneousChartNativeTriplePullbackIntake

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false
variable {X B : Scheme.{u}} (F : X ⟶ B) (U V Z : X.Opens) (n : ℕ) [IsSeparated F]
variable (HU HV HZ : Over B)
variable (etaU : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj HU)
variable (etaV : relativeFiniteFlatHilbertFunctor197 (V.ι ≫ F) n ≅ yoneda.obj HV)
variable (etaZ : relativeFiniteFlatHilbertFunctor197 (Z.ι ≫ F) n ≅ yoneda.obj HZ)

/-- Native pair-inclusion pullback carries the ORIGINAL base map through
its actual first projection to the original U/V parameter overlap. -/
def relativeOpenChartParameterNativeTripleTest001 : Over B :=
  Over.mk (pullback.fst
    (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
    (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left ≫
      (relativeOpenChartParameterOverlapTest001 F U V n HU etaU).hom)

/-- Actual first projection in the original slice category. -/
def relativeOpenChartParameterNativeTripleToPair001 :
    relativeOpenChartParameterNativeTripleTest001 F U V Z n HU etaU ⟶
      relativeOpenChartParameterOverlapTest001 F U V n HU etaU :=
  Over.homMk (pullback.fst
    (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
    (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left) rfl

/-- The original first chart projection of the native triple scheme. -/
def relativeOpenChartParameterNativeTripleToChart001 :
    relativeOpenChartParameterNativeTripleTest001 F U V Z n HU etaU ⟶ HU :=
  relativeOpenChartParameterNativeTripleToPair001 F U V Z n HU etaU ≫
    relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU

/-- Native t-prime retains its EXACT original-chart projection; its
actual target pullback condition and reciprocal factor identity prove it. -/
theorem relativeOpenChartParameterNativeTripleMap_chartProjection001 :
    relativeOpenChartParameterNativeTripleMap001 F U V Z n HU HV etaU etaV ≫
      (pullback.fst (relativeOpenChartParameterOverlapInclusion001 F V Z n HV etaV).left
        (relativeOpenChartParameterOverlapInclusion001 F V U n HV etaV).left ≫
          (relativeOpenChartParameterOverlapInclusion001 F V Z n HV etaV).left) =
    pullback.fst (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
      (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left ≫
        (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV).left := by
  let p := relativeOpenChartParameterNativeTripleMap001 F U V Z n HU HV etaU etaV
  let qi := pullback.fst (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
    (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left
  let fj := (relativeOpenChartParameterOverlapInclusion001 F V Z n HV etaV).left
  let gj := (relativeOpenChartParameterOverlapInclusion001 F V U n HV etaV).left
  let r := (relativeOpenChartParameterOverlapReciprocalMap001 F U V n HU HV etaU etaV).left
  have hReciprocal : r ≫ gj =
      (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV).left :=
    congrArg (fun f => f.left) (relativeOpenChartParameterOverlapReciprocalMap_comp001 F U V n HU HV etaU etaV)
  calc
    p ≫ (pullback.fst fj gj ≫ fj) = p ≫ (pullback.snd fj gj ≫ gj) :=
      congrArg (fun f => p ≫ f) (pullback.condition (f := fj) (g := gj))
    _ = (p ≫ pullback.snd fj gj) ≫ gj := (Category.assoc _ _ _).symm
    _ = (qi ≫ r) ≫ gj := congrArg (fun f => f ≫ gj)
      (relativeOpenChartParameterNativeTripleMap_snd001 F U V Z n HU HV etaU etaV)
    _ = qi ≫ (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV).left :=
      (Category.assoc _ _ _).trans (congrArg (fun f => qi ≫ f) hReciprocal)

/-- Native t-prime is a genuine ORIGINAL-base slice map; its base equality
is DERIVED from the actual chart projection and original transition. -/
def relativeOpenChartParameterNativeTripleOverMap001 :
    relativeOpenChartParameterNativeTripleTest001 F U V Z n HU etaU ⟶
      relativeOpenChartParameterNativeTripleTest001 F V Z U n HV etaV := by
  let p := relativeOpenChartParameterNativeTripleMap001 F U V Z n HU HV etaU etaV
  let qi := pullback.fst (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
    (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left
  let qj := pullback.fst (relativeOpenChartParameterOverlapInclusion001 F V Z n HV etaV).left
    (relativeOpenChartParameterOverlapInclusion001 F V U n HV etaV).left
  let fj := (relativeOpenChartParameterOverlapInclusion001 F V Z n HV etaV).left
  let t := relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV
  refine Over.homMk p ?_
  change p ≫ (qj ≫ (fj ≫ HV.hom)) = qi ≫ (relativeOpenChartParameterOverlapTest001 F U V n HU etaU).hom
  calc
    _ = (p ≫ (qj ≫ fj)) ≫ HV.hom := by simp only [Category.assoc]
    _ = (qi ≫ t.left) ≫ HV.hom := congrArg (fun f => f ≫ HV.hom)
      (relativeOpenChartParameterNativeTripleMap_chartProjection001 F U V Z n HU HV etaU etaV)
    _ = qi ≫ (t.left ≫ HV.hom) := Category.assoc _ _ _
    _ = _ := congrArg (fun f => qi ≫ f) (Over.w t)

/-- The native slice map's chart projection is the actual U/V transition,
not a supplied comparison or point-label matching. -/
theorem relativeOpenChartParameterNativeTripleOverMap_toChart001 :
    relativeOpenChartParameterNativeTripleOverMap001 F U V Z n HU HV etaU etaV ≫
      relativeOpenChartParameterNativeTripleToChart001 F V Z U n HV etaV =
    relativeOpenChartParameterNativeTripleToPair001 F U V Z n HU etaU ≫
      relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV := by
  apply Over.OverMorphism.ext
  exact relativeOpenChartParameterNativeTripleMap_chartProjection001 F U V Z n HU HV etaU etaV

/-- Each native triple map preserves the EXACT original whole family,
by actual chart projection, original315 naturality and transition matching. -/
theorem relativeOpenChartParameterNativeTripleOverMap_wholeFamily001 :
    relativeOpenChartClassifiedAmbientPoint001 F V n HV etaV
      (relativeOpenChartParameterNativeTripleTest001 F U V Z n HU etaU)
      (relativeOpenChartParameterNativeTripleOverMap001 F U V Z n HU HV etaU etaV ≫
        relativeOpenChartParameterNativeTripleToChart001 F V Z U n HV etaV) =
    relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU
      (relativeOpenChartParameterNativeTripleTest001 F U V Z n HU etaU)
      (relativeOpenChartParameterNativeTripleToChart001 F U V Z n HU etaU) := by
  rw [relativeOpenChartParameterNativeTripleOverMap_toChart001,
    relativeOpenChartClassifiedAmbientPoint_natural001,
    relativeOpenChartParameterOverlapTransition_classifiedAmbientPoint001]
  exact (relativeOpenChartClassifiedAmbientPoint_natural001 F U n HU etaU
    (relativeOpenChartParameterNativeTripleToPair001 F U V Z n HU etaU)
    (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU)).symm

/-- Cyclic composition of the actual native triple maps is identity OVER
ORIGINAL B, derived by three entire-family coherences and classifier
injectivity, then cancellation of the actual open chart projection. -/
theorem relativeOpenChartParameterNativeTripleOverMap_cyclic001 :
    relativeOpenChartParameterNativeTripleOverMap001 F U V Z n HU HV etaU etaV ≫
      relativeOpenChartParameterNativeTripleOverMap001 F V Z U n HV HZ etaV etaZ ≫
        relativeOpenChartParameterNativeTripleOverMap001 F Z U V n HZ HU etaZ etaU =
      𝟙 (relativeOpenChartParameterNativeTripleTest001 F U V Z n HU etaU) := by
  let Ti := relativeOpenChartParameterNativeTripleTest001 F U V Z n HU etaU
  let Tj := relativeOpenChartParameterNativeTripleTest001 F V Z U n HV etaV
  let Tk := relativeOpenChartParameterNativeTripleTest001 F Z U V n HZ etaZ
  let a := relativeOpenChartParameterNativeTripleOverMap001 F U V Z n HU HV etaU etaV
  let b := relativeOpenChartParameterNativeTripleOverMap001 F V Z U n HV HZ etaV etaZ
  let c := relativeOpenChartParameterNativeTripleOverMap001 F Z U V n HZ HU etaZ etaU
  let gi := relativeOpenChartParameterNativeTripleToChart001 F U V Z n HU etaU
  let gj := relativeOpenChartParameterNativeTripleToChart001 F V Z U n HV etaV
  let gk := relativeOpenChartParameterNativeTripleToChart001 F Z U V n HZ etaZ
  have hC :
      relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU Tk (c ≫ gi) =
        relativeOpenChartClassifiedAmbientPoint001 F Z n HZ etaZ Tk gk :=
    relativeOpenChartParameterNativeTripleOverMap_wholeFamily001 F Z U V n HZ HU etaZ etaU
  have hB :
      relativeOpenChartClassifiedAmbientPoint001 F Z n HZ etaZ Tj (b ≫ gk) =
        relativeOpenChartClassifiedAmbientPoint001 F V n HV etaV Tj gj :=
    relativeOpenChartParameterNativeTripleOverMap_wholeFamily001 F V Z U n HV HZ etaV etaZ
  have hReturn : (a ≫ b ≫ c) ≫ gi = gi := by
    apply relativeOpenChartClassifiedAmbientPoint_injective001 F U n HU etaU Ti
    let P0 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ti) n :=
      relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU Ti ((a ≫ b ≫ c) ≫ gi)
    let P1 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ti) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map a.op
        ((relativeFiniteFlatHilbertFunctor197 F n).map b.op
          (relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU Tk (c ≫ gi)))
    let P2 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ti) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map a.op
        ((relativeFiniteFlatHilbertFunctor197 F n).map b.op
          (relativeOpenChartClassifiedAmbientPoint001 F Z n HZ etaZ Tk gk))
    let P3 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ti) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map a.op
        (relativeOpenChartClassifiedAmbientPoint001 F Z n HZ etaZ Tj (b ≫ gk))
    let P4 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ti) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map a.op
        (relativeOpenChartClassifiedAmbientPoint001 F V n HV etaV Tj gj)
    let P5 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ti) n :=
      relativeOpenChartClassifiedAmbientPoint001 F V n HV etaV Ti (a ≫ gj)
    let P6 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ti) n :=
      relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU Ti gi
    have h0 : P0 = P1 := by
      change relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU Ti ((a ≫ b ≫ c) ≫ gi) =
        (relativeFiniteFlatHilbertFunctor197 F n).map a.op
          ((relativeFiniteFlatHilbertFunctor197 F n).map b.op
            (relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU Tk (c ≫ gi)))
      rw [Category.assoc, Category.assoc,
        relativeOpenChartClassifiedAmbientPoint_natural001,
        relativeOpenChartClassifiedAmbientPoint_natural001]
    have h1 : P1 = P2 :=
      congrArg (fun P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tk) n =>
        (relativeFiniteFlatHilbertFunctor197 F n).map a.op
          ((relativeFiniteFlatHilbertFunctor197 F n).map b.op P)) hC
    have h2 : P2 = P3 :=
      congrArg (fun P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tj) n =>
        (relativeFiniteFlatHilbertFunctor197 F n).map a.op P)
        (relativeOpenChartClassifiedAmbientPoint_natural001 F Z n HZ etaZ b gk).symm
    have h3 : P3 = P4 :=
      congrArg (fun P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tj) n =>
        (relativeFiniteFlatHilbertFunctor197 F n).map a.op P) hB
    have h4 : P4 = P5 :=
      (relativeOpenChartClassifiedAmbientPoint_natural001 F V n HV etaV a gj).symm
    have h5 : P5 = P6 :=
      relativeOpenChartParameterNativeTripleOverMap_wholeFamily001 F U V Z n HU HV etaU etaV
    exact Eq.trans h0 (Eq.trans h1 (Eq.trans h2 (Eq.trans h3 (Eq.trans h4 h5))))
  apply Over.OverMorphism.ext
  letI : Mono (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left := by
    change Mono (relativeOpenChartParameterOverlap001 F U V n HU etaU).ι
    infer_instance
  letI : Mono (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left := by
    change Mono (relativeOpenChartParameterOverlap001 F U Z n HU etaU).ι
    infer_instance
  letI : Mono gi.left := by
    change Mono (pullback.fst
      (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
      (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left ≫
        (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left)
    infer_instance
  apply (cancel_mono gi.left).mp
  exact (congrArg (fun f => f.left) hReturn).trans (Category.id_comp gi.left).symm

/-- EXACT native Scheme.GlueData cyclic identity for the constructed t-prime
maps on literal pair-inclusion pullbacks, with all Scheme structure retained. -/
theorem relativeOpenChartParameterNativeTripleMap_cyclic001 :
    relativeOpenChartParameterNativeTripleMap001 F U V Z n HU HV etaU etaV ≫
      relativeOpenChartParameterNativeTripleMap001 F V Z U n HV HZ etaV etaZ ≫
        relativeOpenChartParameterNativeTripleMap001 F Z U V n HZ HU etaZ etaU =
      𝟙 (pullback (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left
        (relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU).left) :=
  congrArg (fun f => f.left)
    (relativeOpenChartParameterNativeTripleOverMap_cyclic001 F U V Z n HU HV HZ etaU etaV etaZ)

end PfaffianDescent
end

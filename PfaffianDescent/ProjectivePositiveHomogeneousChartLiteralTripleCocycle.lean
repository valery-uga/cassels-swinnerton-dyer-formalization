import PfaffianDescent.ProjectivePositiveHomogeneousChartReciprocalOverlapIso

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Structural open factor, used below ONLY with actual range conditions
internally derived on the literal triple overlap. -/
def relativeParameterOpenRangeFactor001 {B : Scheme.{u}} (H T : Over B)
    (W : H.left.Opens) (g : T ⟶ H) (hRange : Set.range g.left ⊆ (W : Set H.left)) :
    T ⟶ Over.mk (W.ι ≫ H.hom) := by
  have h : Set.range g.left ⊆ Set.range W.ι := by simpa only [W.range_ι] using hRange
  let a := IsOpenImmersion.lift W.ι g.left h
  refine Over.homMk a ?_
  exact (Category.assoc a W.ι H.hom).symm.trans
    ((congrArg (fun f => f ≫ H.hom) (IsOpenImmersion.lift_fac W.ι g.left h)).trans (Over.w g))

/-- The structural factor keeps the original map exactly after inclusion. -/
theorem relativeParameterOpenRangeFactor_comp001 {B : Scheme.{u}} (H T : Over B)
    (W : H.left.Opens) (g : T ⟶ H) (hRange : Set.range g.left ⊆ (W : Set H.left)) :
    relativeParameterOpenRangeFactor001 H T W g hRange ≫ Over.homMk W.ι rfl = g := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

variable {X B : Scheme.{u}} (F : X ⟶ B) (U V Z : X.Opens) (n : ℕ) [IsSeparated F]
variable (HU HV HZ : Over B)
variable (etaU : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj HU)
variable (etaV : relativeFiniteFlatHilbertFunctor197 (V.ι ≫ F) n ≅ yoneda.obj HV)
variable (etaZ : relativeFiniteFlatHilbertFunctor197 (Z.ι ≫ F) n ≅ yoneda.obj HZ)

/-- The literal two descriptions of the TRIPLE parameter overlap agree by
arbitrary good-open basechange and the actual transition's whole matching. -/
theorem relativeOpenChartParameterTriple_preimages_eq001 :
    (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV).left ⁻¹ᵁ
        relativeOpenChartParameterOverlap001 F V Z n HV etaV =
      (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left ⁻¹ᵁ
        relativeOpenChartParameterOverlap001 F U Z n HU etaU := by
  let T := relativeOpenChartParameterOverlapTest001 F U V n HU etaU
  let gV := relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV
  let gU := relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU
  have hV : finiteFamilyWholeOpenLocus314 (relativeHilbertFamily197 F T) n
      (relativeOpenChartClassifiedAmbientPoint001 F V n HV etaV T gV)
      (pullback.snd T.hom F ⁻¹ᵁ Z) =
        gV.left ⁻¹ᵁ relativeOpenChartParameterOverlap001 F V Z n HV etaV := by
    rw [relativeOpenChartClassifiedAmbientPoint_eq_pullback001]
    exact relativeFiniteFlatHilbertWholeOpenLocus_baseChange001 F n Z gV
      (relativeOpenChartUniversalAmbientPoint001 F V n HV etaV)
  have hU : finiteFamilyWholeOpenLocus314 (relativeHilbertFamily197 F T) n
      (relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU T gU)
      (pullback.snd T.hom F ⁻¹ᵁ Z) =
        gU.left ⁻¹ᵁ relativeOpenChartParameterOverlap001 F U Z n HU etaU := by
    rw [relativeOpenChartClassifiedAmbientPoint_eq_pullback001]
    exact relativeFiniteFlatHilbertWholeOpenLocus_baseChange001 F n Z gU
      (relativeOpenChartUniversalAmbientPoint001 F U n HU etaU)
  exact hV.symm.trans ((congrArg (fun P => finiteFamilyWholeOpenLocus314
    (relativeHilbertFamily197 F T) n P (pullback.snd T.hom F ⁻¹ᵁ Z))
      (relativeOpenChartParameterOverlapTransition_classifiedAmbientPoint001 F U V n HU HV etaU etaV)).trans hU)

/-- Actual triple open inside the literal U/V overlap; no supplied cover or
triple incidence is substituted for this original preimage. -/
def relativeOpenChartParameterTripleOpen001 :
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU).left.Opens :=
  (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left ⁻¹ᵁ
    relativeOpenChartParameterOverlap001 F U Z n HU etaU

/-- The literal triple scheme retains its original-base structure map. -/
def relativeOpenChartParameterTripleTest001 : Over B :=
  Over.mk ((relativeOpenChartParameterTripleOpen001 F U V Z n HU etaU).ι ≫
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU).hom)

/-- Actual inclusion of the triple open into the U/V overlap. -/
def relativeOpenChartParameterTripleInclusion001 :
    relativeOpenChartParameterTripleTest001 F U V Z n HU etaU ⟶
      relativeOpenChartParameterOverlapTest001 F U V n HU etaU :=
  Over.homMk (relativeOpenChartParameterTripleOpen001 F U V Z n HU etaU).ι rfl

/-- First triple map lands in U/Z by its defining original open preimage. -/
theorem relativeOpenChartParameterTriple_first_range001 :
    Set.range (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU ≫
      relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left ⊆
        (relativeOpenChartParameterOverlap001 F U Z n HU etaU : Set HU.left) := by
  rintro x ⟨z, rfl⟩
  exact z.property

/-- Second triple map lands in V/Z by the PROVED equality of original
triple opens, not by an assumed cocycle or matching certificate. -/
theorem relativeOpenChartParameterTriple_second_range001 :
    Set.range (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU ≫
      relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV).left ⊆
        (relativeOpenChartParameterOverlap001 F V Z n HV etaV : Set HV.left) := by
  rintro x ⟨z, rfl⟩
  have hz : z.val ∈ (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left ⁻¹ᵁ
      relativeOpenChartParameterOverlap001 F U Z n HU etaU := z.property
  rw [← relativeOpenChartParameterTriple_preimages_eq001 F U V Z n HU HV etaU etaV] at hz
  exact hz

/-- The first actual triple map factors into the literal U/Z parameter open. -/
def relativeOpenChartParameterTripleToFirstOverlap001 :
    relativeOpenChartParameterTripleTest001 F U V Z n HU etaU ⟶
      relativeOpenChartParameterOverlapTest001 F U Z n HU etaU :=
  relativeParameterOpenRangeFactor001 HU
    (relativeOpenChartParameterTripleTest001 F U V Z n HU etaU)
    (relativeOpenChartParameterOverlap001 F U Z n HU etaU)
    (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU ≫
      relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU)
    (relativeOpenChartParameterTriple_first_range001 F U V Z n HU etaU)

/-- The second actual triple map factors into the literal V/Z parameter open. -/
def relativeOpenChartParameterTripleToSecondOverlap001 :
    relativeOpenChartParameterTripleTest001 F U V Z n HU etaU ⟶
      relativeOpenChartParameterOverlapTest001 F V Z n HV etaV :=
  relativeParameterOpenRangeFactor001 HV
    (relativeOpenChartParameterTripleTest001 F U V Z n HU etaU)
    (relativeOpenChartParameterOverlap001 F V Z n HV etaV)
    (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU ≫
      relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV)
    (relativeOpenChartParameterTriple_second_range001 F U V Z n HU HV etaU etaV)

/-- Exact projection identity for the first genuine triple factor. -/
theorem relativeOpenChartParameterTripleToFirstOverlap_comp001 :
    relativeOpenChartParameterTripleToFirstOverlap001 F U V Z n HU etaU ≫
      relativeOpenChartParameterOverlapInclusion001 F U Z n HU etaU =
        relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU ≫
          relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU :=
  relativeParameterOpenRangeFactor_comp001 _ _ _ _ _

/-- Exact projection identity for the second genuine triple factor. -/
theorem relativeOpenChartParameterTripleToSecondOverlap_comp001 :
    relativeOpenChartParameterTripleToSecondOverlap001 F U V Z n HU HV etaU etaV ≫
      relativeOpenChartParameterOverlapInclusion001 F V Z n HV etaV =
        relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU ≫
          relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV :=
  relativeParameterOpenRangeFactor_comp001 _ _ _ _ _

/-- The LITERAL original triple overlap satisfies the transition cocycle.
Whole-family naturality/matching and classifier injectivity DERIVE this
identity; no triple landing or cocycle outcome is a hypothesis. -/
theorem relativeOpenChartParameterTriple_transition_cocycle001 :
    relativeOpenChartParameterTripleToSecondOverlap001 F U V Z n HU HV etaU etaV ≫
        relativeOpenChartParameterOverlapTransition001 F V Z n HV HZ etaV etaZ =
      relativeOpenChartParameterTripleToFirstOverlap001 F U V Z n HU etaU ≫
        relativeOpenChartParameterOverlapTransition001 F U Z n HU HZ etaU etaZ := by
  apply relativeOpenChartClassifiedAmbientPoint_injective001 F Z n HZ etaZ
    (relativeOpenChartParameterTripleTest001 F U V Z n HU etaU)
  have hLeft : relativeOpenChartClassifiedAmbientPoint001 F Z n HZ etaZ
      (relativeOpenChartParameterTripleTest001 F U V Z n HU etaU)
      (relativeOpenChartParameterTripleToSecondOverlap001 F U V Z n HU HV etaU etaV ≫
        relativeOpenChartParameterOverlapTransition001 F V Z n HV HZ etaV etaZ) =
      relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU
        (relativeOpenChartParameterTripleTest001 F U V Z n HU etaU)
        (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU ≫
          relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU) := by
    rw [relativeOpenChartClassifiedAmbientPoint_natural001,
      relativeOpenChartParameterOverlapTransition_classifiedAmbientPoint001,
      ← relativeOpenChartClassifiedAmbientPoint_natural001,
      relativeOpenChartParameterTripleToSecondOverlap_comp001]
    rw [relativeOpenChartClassifiedAmbientPoint_natural001,
      relativeOpenChartParameterOverlapTransition_classifiedAmbientPoint001,
      ← relativeOpenChartClassifiedAmbientPoint_natural001]
  have hRight : relativeOpenChartClassifiedAmbientPoint001 F Z n HZ etaZ
      (relativeOpenChartParameterTripleTest001 F U V Z n HU etaU)
      (relativeOpenChartParameterTripleToFirstOverlap001 F U V Z n HU etaU ≫
        relativeOpenChartParameterOverlapTransition001 F U Z n HU HZ etaU etaZ) =
      relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU
        (relativeOpenChartParameterTripleTest001 F U V Z n HU etaU)
        (relativeOpenChartParameterTripleInclusion001 F U V Z n HU etaU ≫
          relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU) := by
    rw [relativeOpenChartClassifiedAmbientPoint_natural001,
      relativeOpenChartParameterOverlapTransition_classifiedAmbientPoint001,
      ← relativeOpenChartClassifiedAmbientPoint_natural001,
      relativeOpenChartParameterTripleToFirstOverlap_comp001]
  exact hLeft.trans hRight.symm

/-- Actual positive homogeneous chart models and their literal triple
cocycle are CONSTRUCTED internally over the ORIGINAL Noetherian base. -/
theorem originalPositiveHomogeneousCharts_exists_literalTripleCocycle001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (a b c : CoordinateRing I) (da db dc : ℕ)
    (hda : 0 < da) (ha : a ∈ grading I da) (hdb : 0 < db) (hb : b ∈ grading I db)
    (hdc : 0 < dc) (hc : c ∈ grading I dc) (n : ℕ) (hn : 0 < n) :
    ∃ HU HV HZ : Over (Spec (.of R)),
    ∃ etaU : relativeFiniteFlatHilbertFunctor197 ((Proj.basicOpen (grading I) a).ι ≫ toBase I) n ≅ yoneda.obj HU,
    ∃ etaV : relativeFiniteFlatHilbertFunctor197 ((Proj.basicOpen (grading I) b).ι ≫ toBase I) n ≅ yoneda.obj HV,
    ∃ etaZ : relativeFiniteFlatHilbertFunctor197 ((Proj.basicOpen (grading I) c).ι ≫ toBase I) n ≅ yoneda.obj HZ,
      relativeOpenChartParameterTripleToSecondOverlap001 (toBase I)
        (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) (Proj.basicOpen (grading I) c)
        n HU HV etaU etaV ≫ relativeOpenChartParameterOverlapTransition001 (toBase I)
          (Proj.basicOpen (grading I) b) (Proj.basicOpen (grading I) c) n HV HZ etaV etaZ =
      relativeOpenChartParameterTripleToFirstOverlap001 (toBase I)
        (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) (Proj.basicOpen (grading I) c)
        n HU etaU ≫ relativeOpenChartParameterOverlapTransition001 (toBase I)
          (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) c) n HU HZ etaU etaZ := by
  obtain ⟨HU, hU⟩ := originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I a da hda ha n hn
  obtain ⟨HV, hV⟩ := originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I b db hdb hb n hn
  obtain ⟨HZ, hZ⟩ := originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I c dc hdc hc n hn
  let etaU := Classical.choice hU
  let etaV := Classical.choice hV
  let etaZ := Classical.choice hZ
  exact ⟨HU, HV, HZ, etaU, etaV, etaZ,
    relativeOpenChartParameterTriple_transition_cocycle001 (toBase I)
      (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) (Proj.basicOpen (grading I) c)
      n HU HV HZ etaU etaV etaZ⟩

end PfaffianDescent
end

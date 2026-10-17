import PfaffianDescent.RelativeOpenChartClassifierAmbientCoherence
import PfaffianDescent.ProjectivePositiveHomogeneousChartWholeTransition

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
variable {X B : Scheme.{u}} (F : X ⟶ B) (U V : X.Opens) (n : ℕ) [IsSeparated F]
variable (HU HV : Over B)
variable (etaU : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj HU)
variable (etaV : relativeFiniteFlatHilbertFunctor197 (V.ι ≫ F) n ≅ yoneda.obj HV)

/-- The actual transition's classified family is the very SAME whole
ambient family classified by the original overlap inclusion. -/
theorem relativeOpenChartParameterOverlapTransition_classifiedAmbientPoint001 :
    relativeOpenChartClassifiedAmbientPoint001 F V n HV etaV
      (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
      (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV) =
    relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU
      (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
      (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU) := by
  apply Subtype.ext
  exact (relativeOpenFiniteFlatPointPush_wholeIdeal315 V F n
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
    (etaV.inv.app (.op (relativeOpenChartParameterOverlapTest001 F U V n HU etaU))
      (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV))).trans
    (relativeOpenChartParameterOverlapTransition_wholeAmbientIdeal001 F U V n HU HV etaU etaV)

/-- Reciprocal-overlap landing follows from actual whole-family matching
and OWN-chart containment; no range or inverse certificate is supplied. -/
theorem relativeOpenChartParameterOverlapTransition_range_in_reciprocal001 :
    Set.range (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV).left ⊆
      (relativeOpenChartParameterOverlap001 F V U n HV etaV : Set HV.left) := by
  apply (relativeOpenChartParameterOverlap_range_iff_entireFamily001 F V U n HV etaV
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
    (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV)).mpr
  rw [relativeOpenChartParameterOverlapTransition_classifiedAmbientPoint001]
  exact relativeOpenChartClassifiedAmbientPoint_entireSource_in_ownChart001 F U n HU etaU
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
    (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU)

/-- The open immersion's actual universal property CONSTRUCTS the slice
map to the reciprocal overlap, preserving the ORIGINAL base morphism. -/
def relativeOpenChartParameterOverlapReciprocalMap001 :
    relativeOpenChartParameterOverlapTest001 F U V n HU etaU ⟶
      relativeOpenChartParameterOverlapTest001 F V U n HV etaV := by
  let W := relativeOpenChartParameterOverlap001 F V U n HV etaV
  let t := relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV
  have hr : Set.range t.left ⊆ Set.range W.ι := by
    simpa only [W.range_ι] using
      relativeOpenChartParameterOverlapTransition_range_in_reciprocal001 F U V n HU HV etaU etaV
  let a := IsOpenImmersion.lift W.ι t.left hr
  refine Over.homMk a ?_
  change a ≫ (W.ι ≫ HV.hom) = (relativeOpenChartParameterOverlapTest001 F U V n HU etaU).hom
  exact (Category.assoc a W.ι HV.hom).symm.trans
    ((congrArg (fun f => f ≫ HV.hom) (IsOpenImmersion.lift_fac W.ι t.left hr)).trans (Over.w t))

/-- The derived reciprocal factor retains the EXACT actual transition map. -/
theorem relativeOpenChartParameterOverlapReciprocalMap_comp001 :
    relativeOpenChartParameterOverlapReciprocalMap001 F U V n HU HV etaU etaV ≫
      relativeOpenChartParameterOverlapInclusion001 F V U n HV etaV =
        relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV := by
  apply Over.OverMorphism.ext
  let W := relativeOpenChartParameterOverlap001 F V U n HV etaV
  let t := relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV
  letI : IsOpenImmersion W.ι :=
    inferInstanceAs (IsOpenImmersion (HV.left.ofRestrict W.isOpenEmbedding))
  have hr : Set.range t.left ⊆ Set.range W.ι := by
    simpa only [W.range_ι] using
      relativeOpenChartParameterOverlapTransition_range_in_reciprocal001 F U V n HU HV etaU etaV
  change IsOpenImmersion.lift W.ι t.left hr ≫ W.ι = t.left
  exact IsOpenImmersion.lift_fac W.ι t.left hr

/-- Return transition recovers the original overlap inclusion, by actual
whole-family naturality and classifier injectivity. -/
theorem relativeOpenChartParameterOverlapReciprocalMap_returnTransition001 :
    relativeOpenChartParameterOverlapReciprocalMap001 F U V n HU HV etaU etaV ≫
      relativeOpenChartParameterOverlapTransition001 F V U n HV HU etaV etaU =
        relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU := by
  apply relativeOpenChartClassifiedAmbientPoint_injective001 F U n HU etaU
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
  rw [relativeOpenChartClassifiedAmbientPoint_natural001,
    relativeOpenChartParameterOverlapTransition_classifiedAmbientPoint001]
  rw [← relativeOpenChartClassifiedAmbientPoint_natural001,
    relativeOpenChartParameterOverlapReciprocalMap_comp001]
  exact relativeOpenChartParameterOverlapTransition_classifiedAmbientPoint001 F U V n HU HV etaU etaV

/-- The two actual reciprocal factors are inverse on their SAME whole
parameter opens. Their identities are DERIVED, not matching hypotheses. -/
theorem relativeOpenChartParameterOverlapReciprocalMap_comp_swap001 :
    relativeOpenChartParameterOverlapReciprocalMap001 F U V n HU HV etaU etaV ≫
      relativeOpenChartParameterOverlapReciprocalMap001 F V U n HV HU etaV etaU =
        𝟙 (relativeOpenChartParameterOverlapTest001 F U V n HU etaU) := by
  let i := relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU
  have hi : (relativeOpenChartParameterOverlapReciprocalMap001 F U V n HU HV etaU etaV ≫
      relativeOpenChartParameterOverlapReciprocalMap001 F V U n HV HU etaV etaU) ≫ i = i := by
    rw [Category.assoc, relativeOpenChartParameterOverlapReciprocalMap_comp001]
    exact relativeOpenChartParameterOverlapReciprocalMap_returnTransition001 F U V n HU HV etaU etaV
  apply Over.OverMorphism.ext
  letI : Mono i.left := by
    change Mono (relativeOpenChartParameterOverlap001 F U V n HU etaU).ι
    infer_instance
  apply (cancel_mono i.left).mp
  exact (congrArg (fun f => f.left) hi).trans (Category.id_comp i.left).symm

/-- Constructed isomorphism between the two literal reciprocal parameter
opens OVER the ORIGINAL base, retaining the actual transition as its inclusion. -/
def relativeOpenChartParameterOverlapReciprocalIso001 :
    relativeOpenChartParameterOverlapTest001 F U V n HU etaU ≅
      relativeOpenChartParameterOverlapTest001 F V U n HV etaV where
  hom := relativeOpenChartParameterOverlapReciprocalMap001 F U V n HU HV etaU etaV
  inv := relativeOpenChartParameterOverlapReciprocalMap001 F V U n HV HU etaV etaU
  hom_inv_id := relativeOpenChartParameterOverlapReciprocalMap_comp_swap001 F U V n HU HV etaU etaV
  inv_hom_id := relativeOpenChartParameterOverlapReciprocalMap_comp_swap001 F V U n HV HU etaV etaU

/-- Actual original positive homogeneous chart models and their reciprocal
open isomorphism are constructed internally. No classifier, reciprocal
landing, factor, inverse or matching outcome is a premise. -/
theorem originalPositiveHomogeneousCharts_exists_reciprocalOverlapIso001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (a b : CoordinateRing I) (da db : ℕ)
    (hda : 0 < da) (ha : a ∈ grading I da) (hdb : 0 < db) (hb : b ∈ grading I db)
    (n : ℕ) (hn : 0 < n) :
    ∃ HU HV : Over (Spec (.of R)),
    ∃ etaU : relativeFiniteFlatHilbertFunctor197
        ((Proj.basicOpen (grading I) a).ι ≫ toBase I) n ≅ yoneda.obj HU,
    ∃ etaV : relativeFiniteFlatHilbertFunctor197
        ((Proj.basicOpen (grading I) b).ι ≫ toBase I) n ≅ yoneda.obj HV,
      Nonempty (relativeOpenChartParameterOverlapTest001 (toBase I)
        (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU etaU ≅
        relativeOpenChartParameterOverlapTest001 (toBase I)
          (Proj.basicOpen (grading I) b) (Proj.basicOpen (grading I) a) n HV etaV) := by
  obtain ⟨HU, hU⟩ :=
    originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I a da hda ha n hn
  obtain ⟨HV, hV⟩ :=
    originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I b db hdb hb n hn
  let etaU := Classical.choice hU
  let etaV := Classical.choice hV
  exact ⟨HU, HV, etaU, etaV, ⟨relativeOpenChartParameterOverlapReciprocalIso001 (toBase I)
    (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU HV etaU etaV⟩⟩

end PfaffianDescent
end

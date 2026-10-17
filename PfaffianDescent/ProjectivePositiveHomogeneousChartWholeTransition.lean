import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterOverlap
import PfaffianDescent.RelativeProjectiveAffineOpenTestIdentification
import PfaffianDescent.RelativeOpenContainedFiniteFlatFunctor315
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Types.Basic

/-! Construct the transition from the actual parameter overlap's universal
WHOLE family into the second chart's representing object. The original
base, scheme-test embeddings and entire ideal are retained. The actual
projective-chart caller constructs both classifiers internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The literal original-chart test embedding has precisely the actual
original-open preimage as its range, through the constructed6329 Scheme iso. -/
private theorem originalOpenTestEmbedding_range_eq_preimage001
    {X B : Scheme.{u}} (F : X ⟶ B) (V : X.Opens) (T : Over B) :
    Set.range (relativeClosedAmbientTestMap313 V.ι F T) =
      (pullback.snd T.hom F ⁻¹ᵁ V : (pullback T.hom F).Opens) := by
  have h := AlgebraicGeometry.range_eq_range_of_surjective
    (relativeOriginalOpenTestPreimage001 V F T).ι
    (relativeClosedAmbientTestMap313 V.ι F T)
    (relativeOriginalOpenTestPreimageIso001 V F T).hom
    (relativeOriginalOpenTestPreimageIso_toAmbient001 V F T)
  exact h.symm.trans (relativeOriginalOpenTestPreimage001 V F T).range_ι

variable {X B : Scheme.{u}} (F : X ⟶ B) (U V : X.Opens) (n : ℕ) [IsSeparated F]
variable (HU HV : Over B)
variable (etaU : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj HU)
variable (etaV : relativeFiniteFlatHilbertFunctor197 (V.ι ≫ F) n ≅ yoneda.obj HV)

/-- The overlap is a literal scheme over the ORIGINAL base, via its actual
open inclusion into HU followed by HU's original structure map. -/
def relativeOpenChartParameterOverlapTest001 : Over B :=
  Over.mk ((relativeOpenChartParameterOverlap001 F U V n HU etaU).ι ≫ HU.hom)

/-- Actual overlap inclusion in the original slice category. -/
def relativeOpenChartParameterOverlapInclusion001 :
    relativeOpenChartParameterOverlapTest001 F U V n HU etaU ⟶ HU :=
  Over.homMk (relativeOpenChartParameterOverlap001 F U V n HU etaU).ι rfl

/-- Whole second-chart containment follows from the constructed maximal
open criterion and literal overlap inclusion; it is not a premise. -/
private theorem relativeOpenChartParameterOverlapUniversal_in_secondChart001 :
    Set.range (relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU
      (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
      (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU)).val.subschemeι ⊆
        Set.range (relativeClosedAmbientTestMap313 V.ι F
          (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)) := by
  have hRange : Set.range (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU).left ⊆
      (relativeOpenChartParameterOverlap001 F U V n HU etaU : Set HU.left) := by
    rintro x ⟨z, rfl⟩
    exact z.property
  have hWhole := (relativeOpenChartParameterOverlap_range_iff_entireFamily001 F U V n HU etaU
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
    (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU)).mp hRange
  rw [← originalOpenTestEmbedding_range_eq_preimage001 F V
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)] at hWhole
  exact hWhole

/-- Native315 constructs the literal second-chart point from the ENTIRE
restricted universal ambient family, retaining its original scheme maps. -/
def relativeOpenChartParameterOverlapSecondChartPoint001 :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (V.ι ≫ F)
      (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)) n :=
  (relativeOpenContainedPointEquiv315 V F n
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)).symm
      ⟨relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU
        (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
        (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU),
        relativeOpenChartParameterOverlapUniversal_in_secondChart001 F U V n HU etaU⟩

/-- The actual transition is the second chart's classifier of that
internally constructed point. No transition or matching outcome is assumed. -/
def relativeOpenChartParameterOverlapTransition001 :
    relativeOpenChartParameterOverlapTest001 F U V n HU etaU ⟶ HV :=
  etaV.hom.app (.op (relativeOpenChartParameterOverlapTest001 F U V n HU etaU))
    (relativeOpenChartParameterOverlapSecondChartPoint001 F U V n HU etaU)

/-- Inverse classification at the actual transition recovers EXACTLY the
same ENTIRE original ambient ideal. No radical or reduction is introduced. -/
theorem relativeOpenChartParameterOverlapTransition_wholeAmbientIdeal001 :
    (etaV.inv.app (.op (relativeOpenChartParameterOverlapTest001 F U V n HU etaU))
      (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV)).val.map
        (relativeClosedAmbientTestMap313 V.ι F
          (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)) =
      (relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU
        (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
        (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU)).val := by
  have hInv : etaV.inv.app (.op (relativeOpenChartParameterOverlapTest001 F U V n HU etaU))
      (relativeOpenChartParameterOverlapTransition001 F U V n HU HV etaU etaV) =
        relativeOpenChartParameterOverlapSecondChartPoint001 F U V n HU etaU := by
    exact ConcreteCategory.congr_hom
      (etaV.hom_inv_id_app (.op (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)))
      (relativeOpenChartParameterOverlapSecondChartPoint001 F U V n HU etaU)
  rw [hInv]
  exact relativeOpenContainedPointEquiv_inv_ambientIdeal315 V F n
    (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
    ⟨relativeOpenChartClassifiedAmbientPoint001 F U n HU etaU
      (relativeOpenChartParameterOverlapTest001 F U V n HU etaU)
      (relativeOpenChartParameterOverlapInclusion001 F U V n HU etaU),
      relativeOpenChartParameterOverlapUniversal_in_secondChart001 F U V n HU etaU⟩

/-- Both SAME original positive homogeneous chart classifiers, their actual
parameter overlap and transition are CONSTRUCTED internally over the
ORIGINAL Noetherian base. Exact universal whole-ideal matching is derived.
Neither classifier, transition, overlap, incidence or matching is a premise.
Reciprocal-open factorization, inverse/cocycle and global gluing remain separate. -/
theorem originalPositiveHomogeneousCharts_exists_wholeTransition001
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
    ∃ t : relativeOpenChartParameterOverlapTest001 (toBase I)
        (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU etaU ⟶ HV,
      (etaV.inv.app (.op (relativeOpenChartParameterOverlapTest001 (toBase I)
        (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU etaU)) t).val.map
          (relativeClosedAmbientTestMap313 (Proj.basicOpen (grading I) b).ι (toBase I)
            (relativeOpenChartParameterOverlapTest001 (toBase I)
              (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU etaU)) =
        (relativeOpenChartClassifiedAmbientPoint001 (toBase I) (Proj.basicOpen (grading I) a)
          n HU etaU (relativeOpenChartParameterOverlapTest001 (toBase I)
            (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU etaU)
          (relativeOpenChartParameterOverlapInclusion001 (toBase I)
            (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU etaU)).val := by
  obtain ⟨HU, hU⟩ :=
    originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I a da hda ha n hn
  obtain ⟨HV, hV⟩ :=
    originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I b db hdb hb n hn
  let etaU := Classical.choice hU
  let etaV := Classical.choice hV
  refine ⟨HU, HV, etaU, etaV, relativeOpenChartParameterOverlapTransition001 (toBase I)
    (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU HV etaU etaV, ?_⟩
  exact relativeOpenChartParameterOverlapTransition_wholeAmbientIdeal001 (toBase I)
    (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n HU HV etaU etaV

end PfaffianDescent
end

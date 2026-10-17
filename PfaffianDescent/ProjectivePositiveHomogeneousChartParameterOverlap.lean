import PfaffianDescent.ProjectivePositiveHomogeneousChartAllTestClassifier
import PfaffianDescent.NativeWholeFiniteFamilyOpenLocusCartesianBaseChange
import PfaffianDescent.RelativeOpenContainedFiniteFlatFunctor315
import Mathlib.CategoryTheory.Types.Basic

/-! Construct the actual parameter overlap from the inverse classifier's
universal WHOLE family and the maximal native good open. Arbitrary test
factorization is characterized by the entire family lying in the second
original chart. The concrete projective-chart caller constructs its
representing object and classifier internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Open preimage is the whole source exactly when the actual map has range
in that open. No map into the open is assumed or chosen. -/
private theorem actualOpen_preimage_eq_top_iff_range001
    {S T : Scheme.{u}} (g : S ⟶ T) (W : T.Opens) :
    g ⁻¹ᵁ W = ⊤ ↔ Set.range g ⊆ (W : Set T) := by
  constructor
  · intro h x hx
    obtain ⟨s, rfl⟩ := hx
    have hs : s ∈ g ⁻¹ᵁ W := by rw [h]; trivial
    exact hs
  · intro h
    apply top_unique
    intro s _
    exact h ⟨s, rfl⟩

variable {X B : Scheme.{u}} (F : X ⟶ B) (U V : X.Opens) (n : ℕ) [IsSeparated F]
variable (H : Over B)
variable (eta : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj H)

/-- The classifier inverse gives a literal chart family, pushed through the
actual original open embedding as an ENTIRE closed finite-flat family. -/
def relativeOpenChartClassifiedAmbientPoint001 (T : Over B) (g : T ⟶ H) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n :=
  relativeOpenFiniteFlatPointPush315 U F n T (eta.inv.app (.op T) g)

/-- The actual ambient universal whole family is obtained at the identity
of the constructed chart's representing object. -/
def relativeOpenChartUniversalAmbientPoint001 :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F H) n :=
  relativeOpenChartClassifiedAmbientPoint001 F U n H eta H (𝟙 H)

/-- Classifier naturality and the native315 whole-family push show that
EVERY test family is the literal pullback of this same universal family. -/
theorem relativeOpenChartClassifiedAmbientPoint_eq_pullback001
    (T : Over B) (g : T ⟶ H) :
    relativeOpenChartClassifiedAmbientPoint001 F U n H eta T g =
      (relativeFiniteFlatHilbertFunctor197 F n).map g.op
        (relativeOpenChartUniversalAmbientPoint001 F U n H eta) := by
  have hChart : eta.inv.app (.op T) g =
      (relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n).map g.op
        (eta.inv.app (.op H) (𝟙 H)) := by
    have h := ConcreteCategory.congr_hom (eta.inv.naturality g.op) (𝟙 H)
    change eta.inv.app (.op T) (g ≫ 𝟙 H) =
      (relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n).map g.op
        (eta.inv.app (.op H) (𝟙 H)) at h
    simpa only [Category.comp_id] using h
  change relativeOpenFiniteFlatPointPush315 U F n T (eta.inv.app (.op T) g) = _
  rw [hChart]
  exact relativeOpenFiniteFlatPointPush_natural315 U F n g (eta.inv.app (.op H) (𝟙 H))

/-- The actual parameter overlap is an OPEN in H, constructed from the
universal entire family and the original second chart's literal preimage. -/
def relativeOpenChartParameterOverlap001 : H.left.Opens :=
  finiteFamilyWholeOpenLocus314 (relativeHilbertFamily197 F H) n
    (relativeOpenChartUniversalAmbientPoint001 F U n H eta)
    (pullback.snd H.hom F ⁻¹ᵁ V)

/-- On ALL actual scheme tests, factorization into the constructed overlap
is exactly entire-family containment in the second original chart. The
arbitrary Cartesian good-open basechange theorem supplies this equivalence. -/
theorem relativeOpenChartParameterOverlap_range_iff_entireFamily001
    (T : Over B) (g : T ⟶ H) :
    Set.range g.left ⊆ (relativeOpenChartParameterOverlap001 F U V n H eta : Set H.left) ↔
      Set.range (relativeOpenChartClassifiedAmbientPoint001 F U n H eta T g).val.subschemeι ⊆
        (pullback.snd T.hom F ⁻¹ᵁ V : (pullback T.hom F).Opens) := by
  rw [← actualOpen_preimage_eq_top_iff_range001,
    ← finiteFamilyWholeOpenLocus_eq_top_iff_entireSource_in_open001]
  rw [relativeOpenChartClassifiedAmbientPoint_eq_pullback001]
  exact (congrArg (fun W : T.left.Opens => W = ⊤)
    (relativeFiniteFlatHilbertWholeOpenLocus_baseChange001 F n V g
      (relativeOpenChartUniversalAmbientPoint001 F U n H eta))).symm.to_iff

/-- The SAME actual positive homogeneous chart classifier and its parameter
open overlap are CONSTRUCTED over the original Noetherian base. No
representing scheme, classifier, universal family, good open or containment
outcome is a premise. All test maps and complete original family ideals are
retained. This is an overlap construction, not yet global gluing. -/
theorem originalPositiveHomogeneousChart_exists_parameterOverlap_allTests001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (a b : CoordinateRing I) (d : ℕ) (hd : 0 < d) (ha : a ∈ grading I d)
    (n : ℕ) (hn : 0 < n) :
    ∃ H : Over (Spec (.of R)),
    ∃ eta : relativeFiniteFlatHilbertFunctor197
        ((Proj.basicOpen (grading I) a).ι ≫ toBase I) n ≅ yoneda.obj H,
    ∃ W : H.left.Opens,
      W = relativeOpenChartParameterOverlap001 (toBase I)
        (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n H eta ∧
      ∀ (T : Over (Spec (.of R))) (g : T ⟶ H),
        Set.range g.left ⊆ (W : Set H.left) ↔
          Set.range (relativeOpenChartClassifiedAmbientPoint001 (toBase I)
            (Proj.basicOpen (grading I) a) n H eta T g).val.subschemeι ⊆
              (pullback.snd T.hom (toBase I) ⁻¹ᵁ Proj.basicOpen (grading I) b :
                (pullback T.hom (toBase I)).Opens) := by
  obtain ⟨H, hEta⟩ :=
    originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I a d hd ha n hn
  let eta := Classical.choice hEta
  refine ⟨H, eta, relativeOpenChartParameterOverlap001 (toBase I)
    (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n H eta, rfl, ?_⟩
  intro T g
  exact relativeOpenChartParameterOverlap_range_iff_entireFamily001 (toBase I)
    (Proj.basicOpen (grading I) a) (Proj.basicOpen (grading I) b) n H eta T g

end PfaffianDescent
end

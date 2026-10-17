import PfaffianDescent.P3CanonicalLaurentTrace
import PfaffianDescent.VoisinP3TopCechExtComparison

/-! # The canonical scalar trace on the actual negative-four Cech complex -/
noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentLocalization LaurentCechCore LaurentCechExact
universe u
variable (K : Type u) [Field K]

/-- The canonical residue coefficient on actual raw top cochains. -/
def p3NegativeFourRawTrace : (p3NegativeTwistCechComplex (K := K) 4).X 3 →+ K :=
  (p3SerreResidueCoefficient K 0).comp (p3NegativeTwistCechTermToLaurent K 4 3)

/-- The canonical trace kills every actual degree-two boundary. -/
theorem p3NegativeFourRawTrace_boundary_eq_zero
    (z : (p3NegativeTwistCechComplex (K := K) 4).X 2) :
    p3NegativeFourRawTrace K ((p3NegativeTwistCechComplex (K := K) 4).d 2 3 z) = 0 := by
  change p3SerreResidueCoefficient K 0
    (p3NegativeTwistCechTermToLaurent K 4 3
      ((p3NegativeTwistCechComplex (K := K) 4).d 2 3 z)) = 0
  rw [p3NegativeTwistCechTermToLaurent_d_two]
  apply p3SerreResidueCoefficient_tupleD2_eq_zero
  intro f a ha
  exact (p3NegativeTwistCechTermToLaurent_support_properties K 4 2 z f a ha).2

/-- Conversely, a canonical-degree top cocycle with zero trace is an actual
raw degree-two boundary. -/
theorem p3NegativeFourRawTrace_zero_iff_boundary (w : P3RawTopCocycle K 4) :
    p3NegativeFourRawTrace K w.1 = 0 ↔
      ∃ z : (p3NegativeTwistCechComplex (K := K) 4).X 2,
        (p3NegativeTwistCechComplex (K := K) 4).d 2 3 z = w.1 := by
  constructor
  · intro ht
    let wL := p3NegativeTwistCechTermToLaurent K 4 3 w.1
    have hs : ∀ f (a : LaurentLocalization.LaurentExponent), a ∈ (wL f).coeff.support →
        totalDegree a = -4 ∧ negativeSupport a ⊆ Set.range f := by
      intro f a ha
      exact p3NegativeTwistCechTermToLaurent_support_properties K 4 3 w.1 f a ha
    have hc : ∀ f, tupleD3 wL f = 0 := by
      intro f
      rw [← congrFun (p3NegativeTwistCechTermToLaurent_d_three K 4 w.1) f, w.2]
      simp
    obtain ⟨zL, hzL, hdiff⟩ :=
      laurent_tuple_exact_three_of_degree_neg_four_of_trace_zero K wL hs hc ht
    obtain ⟨z, hz⟩ := exists_p3NegativeTwistCechTermToLaurent_eq_of_support K 4 2 zL hzL
    refine ⟨z, ?_⟩
    apply p3NegativeTwistCechTermToLaurent_injective K 4 3
    rw [p3NegativeTwistCechTermToLaurent_d_two, hz]
    funext f
    exact hdiff f
  · rintro ⟨z, hz⟩
    rw [← hz]
    exact p3NegativeFourRawTrace_boundary_eq_zero K z

/-- The single scalar trace on actual top cocycles. -/
def p3NegativeFourTopTrace : P3RawTopCocycle K 4 →+ K :=
  (p3NegativeFourRawTrace K).comp (AddSubgroup.subtype _)

private theorem canonicalGenerator_support
    (f : Fin 4 → Fin 4) (a : LaurentLocalization.LaurentExponent)
    (ha : a ∈ (p3SerreLaurentGenerator K 0 f).coeff.support) :
    totalDegree a = -4 ∧ negativeSupport a ⊆ Set.range f := by
  have hcoeff : (p3SerreLaurentGenerator K 0 f).coeff a ≠ 0 :=
    Finsupp.mem_support_iff.mp ha
  have heq : a = p3SerreDualExponent 0 := by
    by_contra hne
    apply hcoeff
    simp [p3SerreLaurentGenerator, AddMonoidAlgebra.coeff_single, hne]
  subst a
  refine ⟨by simp [p3SerreDualExponent_totalDegree], ?_⟩
  rw [p3SerreDualExponent_negativeSupport, Set.range_eq_univ.mpr]
  intro y
  by_contra hy
  have hn : ¬ Function.Surjective f := fun h => hy (h y)
  apply hcoeff
  simp [p3SerreLaurentGenerator, tupleOrientation_eq_zero_of_not_surjective f hn]

/-- The orientation generator realizes every scalar trace, so the trace
normalization is fixed by an actual representative with trace one. -/
theorem p3NegativeFourTopTrace_surjective : Function.Surjective (p3NegativeFourTopTrace K) := by
  intro c
  let g : (Fin 4 → Fin 4) → LaurentLocalization.LaurentPolynomial K := c • p3SerreLaurentGenerator K 0
  have hs : ∀ f (a : LaurentLocalization.LaurentExponent), a ∈ (g f).coeff.support →
      totalDegree a = -4 ∧ negativeSupport a ⊆ Set.range f := by
    intro f a ha
    have hg : (p3SerreLaurentGenerator K 0 f).coeff a ≠ 0 := by
      intro hz
      have hne := Finsupp.mem_support_iff.mp ha
      apply hne
      simp [g, hz]
    exact canonicalGenerator_support K f a (Finsupp.mem_support_iff.mpr hg)
  obtain ⟨w, hw⟩ := exists_p3NegativeTwistCechTermToLaurent_eq_of_support K 4 3 g hs
  have hc : (p3NegativeTwistCechComplex (K := K) 4).d 3 4 w = 0 := by
    apply p3NegativeTwistCechTermToLaurent_injective K 4 4
    rw [p3NegativeTwistCechTermToLaurent_d_three, hw]
    funext f
    have h := congrArg (fun v : LaurentLocalization.LaurentPolynomial K => c • v)
      (p3SerreLaurentGenerator_cocycle K 0 f)
    simpa [g, tupleD3, smul_sub, smul_add] using h
  refine ⟨⟨w, hc⟩, ?_⟩
  change p3SerreResidueCoefficient K 0 (p3NegativeTwistCechTermToLaurent K 4 3 w) = c
  rw [hw]
  change (g id).coeff (p3SerreDualExponent 0) = c
  simp [g, p3SerreLaurentGenerator]

end PfaffianDescent.ProjectiveNegativeTwist

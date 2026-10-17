import PfaffianDescent.VoisinP3TopCechGenerators

/-!
# Simultaneous realization of all top Cech residue coordinates

Finite sums of the orientation generators realize an arbitrary family of
coordinates indexed by degree-two monomials.  Lifting such a Laurent
cocycle back to the raw Cech term proves surjectivity of the explicit residue
coordinate map on top cocycles of `O(-6)`.
-/

noncomputable section

open scoped AddMonoidAlgebra BigOperators

namespace PfaffianDescent

namespace LaurentCechExact

open LaurentLocalization LaurentCechCore

universe u

variable (K : Type u) [Field K]

/-- The finite type indexing quadratic monomials in four variables. -/
abbrev P3QuadraticExponent := {b : Fin 4 →₀ ℕ // b.degree = 2}

noncomputable instance : Fintype P3QuadraticExponent :=
  (Finsupp.finite_of_degree_eq 2).fintype

/-- Laurent top cocycle with a prescribed coordinate at every quadratic
monomial. -/
def p3SerreLaurentCoordinateCocycle
    (c : P3QuadraticExponent → K) :
    (Fin 4 → Fin 4) → LaurentPolynomial K :=
  ∑ b : P3QuadraticExponent, c b • p3SerreLaurentGenerator K b

lemma p3SerreLaurentCoordinateCocycle_support
    (c : P3QuadraticExponent → K)
    (f : Fin 4 → Fin 4) (a : LaurentExponent)
    (ha : a ∈ (p3SerreLaurentCoordinateCocycle K c f).coeff.support) :
    totalDegree a = -6 ∧ negativeSupport a ⊆ Set.range f := by
  let q : P3QuadraticExponent → LaurentPolynomial K :=
    fun b => c b • p3SerreLaurentGenerator K b f
  have ha' : a ∈ (∑ b, (q b).coeff).support := by
    simpa [p3SerreLaurentCoordinateCocycle, q] using ha
  have haUnion := Finsupp.support_finsetSum ha'
  obtain ⟨b, _hb, hab⟩ := Finset.mem_biUnion.mp haUnion
  have hgen : a ∈ (p3SerreLaurentGenerator K b f).coeff.support := by
    rw [Finsupp.mem_support_iff] at hab ⊢
    intro hzero
    apply hab
    simp [q, hzero]
  exact p3SerreLaurentGenerator_support K b b.property f a hgen

lemma p3SerreLaurentCoordinateCocycle_cocycle
    (c : P3QuadraticExponent → K) (f : Fin 5 → Fin 4) :
    tupleD3 (p3SerreLaurentCoordinateCocycle K c) f = 0 := by
  simp only [p3SerreLaurentCoordinateCocycle, tupleD3,
    Finset.sum_apply, Pi.smul_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _hb
  rw [← smul_sub, ← smul_add, ← smul_sub, ← smul_add,
    show p3SerreLaurentGenerator K b ![f 1, f 2, f 3, f 4] -
        p3SerreLaurentGenerator K b ![f 0, f 2, f 3, f 4] +
        p3SerreLaurentGenerator K b ![f 0, f 1, f 3, f 4] -
        p3SerreLaurentGenerator K b ![f 0, f 1, f 2, f 4] +
        p3SerreLaurentGenerator K b ![f 0, f 1, f 2, f 3] = 0 from
      p3SerreLaurentGenerator_cocycle K b f,
    smul_zero]

@[simp]
lemma p3SerreResidueCoefficient_coordinateCocycle
    (c : P3QuadraticExponent → K) (b : P3QuadraticExponent) :
    p3SerreResidueCoefficient K b
      (p3SerreLaurentCoordinateCocycle K c) = c b := by
  change ((∑ d : P3QuadraticExponent,
    c d • p3SerreLaurentGenerator K d) id).coeff
      (p3SerreDualExponent b) = c b
  rw [Finset.sum_apply, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply]
  simp only [Pi.smul_apply, AddMonoidAlgebra.coeff_smul]
  rw [Finset.sum_eq_single b]
  · have hself := p3SerreResidueCoefficient_generator_self K b
    change (p3SerreLaurentGenerator K b id).coeff
      (p3SerreDualExponent b) = 1 at hself
    change c b * (p3SerreLaurentGenerator K b id).coeff
      (p3SerreDualExponent b) = c b
    rw [hself, mul_one]
  · intro d _hd hdb
    have hexp : p3SerreDualExponent b ≠ p3SerreDualExponent d := by
      intro h
      exact hdb (Subtype.ext (p3SerreDualExponent_injective h).symm)
    change c d * (p3SerreLaurentGenerator K d id).coeff
      (p3SerreDualExponent b) = 0
    have hcoeff : (p3SerreLaurentGenerator K d id).coeff
        (p3SerreDualExponent b) = 0 := by
      simp [p3SerreLaurentGenerator, hexp.symm]
    rw [hcoeff, mul_zero]
  · intro hb
    simp at hb

end LaurentCechExact

namespace ProjectiveNegativeTwist

open LaurentLocalization LaurentCechCore LaurentCechExact

universe u

variable (K : Type u) [Field K]

/-- A raw top Cech cochain realizing an arbitrary family of quadratic
residue coordinates. -/
noncomputable def p3NegativeSixRawCoordinateCocycle
    (c : P3QuadraticExponent → K) :
    (p3NegativeTwistCechComplex (K := K) 6).X 3 :=
  Classical.choose
    (exists_p3NegativeTwistCechTermToLaurent_eq_of_support K 6 3
      (p3SerreLaurentCoordinateCocycle K c)
      (p3SerreLaurentCoordinateCocycle_support K c))

lemma p3NegativeSixRawCoordinateCocycle_toLaurent
    (c : P3QuadraticExponent → K) :
    p3NegativeTwistCechTermToLaurent K 6 3
        (p3NegativeSixRawCoordinateCocycle K c) =
      p3SerreLaurentCoordinateCocycle K c :=
  Classical.choose_spec
    (exists_p3NegativeTwistCechTermToLaurent_eq_of_support K 6 3
      (p3SerreLaurentCoordinateCocycle K c)
      (p3SerreLaurentCoordinateCocycle_support K c))

lemma p3NegativeSixRawCoordinateCocycle_isCocycle
    (c : P3QuadraticExponent → K) :
    (p3NegativeTwistCechComplex (K := K) 6).d 3 4
      (p3NegativeSixRawCoordinateCocycle K c) = 0 := by
  apply p3NegativeTwistCechTermToLaurent_injective K 6 4
  rw [p3NegativeTwistCechTermToLaurent_d_three K 6,
    p3NegativeSixRawCoordinateCocycle_toLaurent K c]
  funext f
  rw [p3SerreLaurentCoordinateCocycle_cocycle K c f]
  simp

@[simp]
lemma p3NegativeSixRawResidue_coordinateCocycle
    (c : P3QuadraticExponent → K) (b : P3QuadraticExponent) :
    p3NegativeSixRawResidue K b
      (p3NegativeSixRawCoordinateCocycle K c) = c b := by
  rw [p3NegativeSixRawResidue_apply,
    p3NegativeSixRawCoordinateCocycle_toLaurent]
  exact p3SerreResidueCoefficient_coordinateCocycle K c b

/-- Every family of quadratic residue coordinates is simultaneously
realized by a raw top Cech cocycle of `O(-6)`. -/
theorem p3NegativeSixRawResidue_surjective_on_cocycles
    (c : P3QuadraticExponent → K) :
    ∃ w : (p3NegativeTwistCechComplex (K := K) 6).X 3,
      (p3NegativeTwistCechComplex (K := K) 6).d 3 4 w = 0 ∧
      ∀ b : P3QuadraticExponent,
        p3NegativeSixRawResidue K b w = c b := by
  refine ⟨p3NegativeSixRawCoordinateCocycle K c,
    p3NegativeSixRawCoordinateCocycle_isCocycle K c, ?_⟩
  intro b
  exact p3NegativeSixRawResidue_coordinateCocycle K c b

end ProjectiveNegativeTwist

end PfaffianDescent

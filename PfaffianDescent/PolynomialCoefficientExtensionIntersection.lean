import PfaffianDescent.PolynomialCoefficientLinearProjection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! SOURCE ONLY, UNVERIFIED. Coefficient extension across ANY field
extension preserves the literal INTERSECTION of arbitrary polynomial ideals.
The basis may be infinite; only the finitely many coefficient coordinates
of the given polynomial are summed. No point support, radical or flatness
certificate substitutes for equality of the whole ideals. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial
open scoped BigOperators
universe u v w
variable {E K : Type u} [Field E] [Field K] [Algebra E K]
variable {J : Type v}

def basisCoefficientLinearMap {I : Type w} (b : Basis I E K) (i : I) : K →ₗ[E] E :=
  (Finsupp.lapply i).comp b.repr.toLinearMap

@[simp] theorem basisCoefficientLinearMap_apply {I : Type w}
    (b : Basis I E K) (i : I) (z : K) :
    basisCoefficientLinearMap b i z = b.repr z i := rfl

theorem polynomial_eq_finite_sum_coefficientProjections {I : Type w}
    (b : Basis I E K) (q : MvPolynomial J K) :
    ∃ S : Finset I, q = ∑ i ∈ S, C (b i) *
      MvPolynomial.map (algebraMap E K)
        (coefficientPolynomialProjection (basisCoefficientLinearMap b i) q) := by
  classical
  let S : Finset I := q.support.biUnion (fun d => (b.repr (q.coeff d)).support)
  refine ⟨S, ?_⟩
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, coefficientPolynomialProjection_coeff,
    basisCoefficientLinearMap_apply]
  by_cases hd : d ∈ q.support
  · have hsub : (b.repr (q.coeff d)).support ⊆ S := by
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨d, hd, hi⟩
    have hrepr := b.linearCombination_repr (q.coeff d)
    change (∑ i ∈ (b.repr (q.coeff d)).support,
      b.repr (q.coeff d) i • b i) = q.coeff d at hrepr
    have heq : (∑ i ∈ (b.repr (q.coeff d)).support,
        b i * algebraMap E K (b.repr (q.coeff d) i)) =
        ∑ i ∈ S, b i * algebraMap E K (b.repr (q.coeff d) i) := by
      apply Finset.sum_subset hsub
      intro i hi hin
      have hz : b.repr (q.coeff d) i = 0 := Finsupp.notMem_support_iff.mp hin
      simp only [hz, map_zero, mul_zero]
    have hrepr' : q.coeff d = ∑ i ∈ (b.repr (q.coeff d)).support,
        b i * algebraMap E K (b.repr (q.coeff d) i) := by
      simpa only [Algebra.smul_def, mul_comm] using hrepr.symm
    exact hrepr'.trans heq
  · have hz : q.coeff d = 0 := MvPolynomial.notMem_support_iff.mp hd
    simp only [hz, map_zero, Finsupp.zero_apply, mul_zero, Finset.sum_const_zero]

theorem mvPolynomial_coefficientExtension_map_inf
    (I H : Ideal (MvPolynomial J E)) :
    (I ⊓ H).map (MvPolynomial.map (algebraMap E K)) =
      I.map (MvPolynomial.map (algebraMap E K)) ⊓
        H.map (MvPolynomial.map (algebraMap E K)) := by
  classical
  apply le_antisymm (Ideal.map_inf_le _)
  intro q hq
  let b := Module.Free.chooseBasis E K
  obtain ⟨S, hS⟩ := polynomial_eq_finite_sum_coefficientProjections b q
  rw [hS]
  apply Ideal.sum_mem
  intro i hi
  apply Ideal.mul_mem_left
  apply Ideal.mem_map_of_mem
  exact ⟨coefficientPolynomialProjection_mem_of_mem_extendedIdeal _ I q hq.1,
    coefficientPolynomialProjection_mem_of_mem_extendedIdeal _ H q hq.2⟩

end PfaffianDescent

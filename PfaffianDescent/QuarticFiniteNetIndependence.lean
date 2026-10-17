import PfaffianDescent.QuarticFiniteNet

/-!
# Independence of the finite tangent net

The coefficient arguments are split into small lemmas so Lean checks the
symbolic calculation within its ordinary heartbeat budget.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

section
variable {K : Type*} [Field K]

private def scaledNetLinearRelation (a b c d e f : K)
    (q : Fin 3 × Fin 4 → K) : Prop :=
  ∑ ij, q ij • linearQuadricProducts (scaledBaseLocusQuadricPolynomials a b c d e f) ij = 0

private theorem scaledNet_coeff_u1 (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hq : scaledNetLinearRelation a b c d e f q) :
    q (0, 1) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 1 2 + Finsupp.single 2 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, ha, hb] using h

private theorem scaledNet_coeff_u2 (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hq : scaledNetLinearRelation a b c d e f q) :
    q (0, 2) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 1 1 + Finsupp.single 2 2)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, ha, hb] using h

private theorem scaledNet_coeff_v1 (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (ha : a ≠ 0) (hc : c ≠ 0) (hq : scaledNetLinearRelation a b c d e f q) :
    q (1, 1) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 1 2 + Finsupp.single 3 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, ha, hc] using h

private theorem scaledNet_coeff_v3 (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (ha : a ≠ 0) (hc : c ≠ 0) (hq : scaledNetLinearRelation a b c d e f q) :
    q (1, 3) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 1 1 + Finsupp.single 3 2)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, ha, hc] using h

private theorem scaledNet_coeff_w2 (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (hb : b ≠ 0) (hc : c ≠ 0) (hq : scaledNetLinearRelation a b c d e f q) :
    q (2, 2) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 2 2 + Finsupp.single 3 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, hb, hc] using h

private theorem scaledNet_coeff_w3 (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (hb : b ≠ 0) (hc : c ≠ 0) (hq : scaledNetLinearRelation a b c d e f q) :
    q (2, 3) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 2 1 + Finsupp.single 3 2)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, hb, hc] using h

private theorem scaledNet_coeff_E (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (hq : scaledNetLinearRelation a b c d e f q) :
    b * d * q (0, 0) + c * e * q (1, 0) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 2 + Finsupp.single 1 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, mul_comm, mul_left_comm,
    mul_assoc] using h

private theorem scaledNet_coeff_F (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (hq : scaledNetLinearRelation a b c d e f q) :
    -a * d * q (0, 0) + c * f * q (2, 0) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 2 + Finsupp.single 2 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, mul_comm, mul_left_comm,
    mul_assoc] using h


private theorem scaledNet_coeff_A (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (hq : scaledNetLinearRelation a b c d e f q)
    (hu1 : q (0, 1) = 0) (hu2 : q (0, 2) = 0)
    (hv1 : q (1, 1) = 0) (hv3 : q (1, 3) = 0)
    (hw2 : q (2, 2) = 0) (hw3 : q (2, 3) = 0) :
    a * b * q (0, 0) + c * e * q (1, 2) + c * f * q (2, 1) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply,
    hu1, hu2, hv1, hv3, hw2, hw3, mul_comm, mul_left_comm, mul_assoc] using h


private theorem scaledNet_coeff_B (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (hq : scaledNetLinearRelation a b c d e f q)
    (hu1 : q (0, 1) = 0) (hu2 : q (0, 2) = 0)
    (hv1 : q (1, 1) = 0) (hv3 : q (1, 3) = 0)
    (hw2 : q (2, 2) = 0) (hw3 : q (2, 3) = 0) :
    b * d * q (0, 3) + a * c * q (1, 0) + -(b * f * q (2, 1)) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply,
    hu1, hu2, hv1, hv3, hw2, hw3, mul_comm, mul_left_comm, mul_assoc] using h


private theorem scaledNet_coeff_C (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (hq : scaledNetLinearRelation a b c d e f q)
    (hu1 : q (0, 1) = 0) (hu2 : q (0, 2) = 0)
    (hv1 : q (1, 1) = 0) (hv3 : q (1, 3) = 0)
    (hw2 : q (2, 2) = 0) (hw3 : q (2, 3) = 0) :
    -a * d * q (0, 3) + -(a * e * q (1, 2)) + b * c * q (2, 0) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 3 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply,
    hu1, hu2, hv1, hv3, hw2, hw3, mul_comm, mul_left_comm, mul_assoc] using h


private theorem scaledNet_coeff_D (a b c d e f : K) (q : Fin 3 × Fin 4 → K)
    (hq : scaledNetLinearRelation a b c d e f q)
    (hu1 : q (0, 1) = 0) (hu2 : q (0, 2) = 0)
    (hv1 : q (1, 1) = 0) (hv3 : q (1, 3) = 0)
    (hw2 : q (2, 2) = 0) (hw3 : q (2, 3) = 0) :
    a * b * q (0, 3) + a * c * q (1, 2) + b * c * q (2, 1) = 0 := by
  unfold scaledNetLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 3 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply,
    hu1, hu2, hv1, hv3, hw2, hw3, mul_comm, mul_left_comm, mul_assoc] using h

/-- The twelve linear multiples of the nonexceptional tangent net are
linearly independent. -/
theorem scaledBaseLocus_linearProducts_independent (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (hdelta : baseLocusDelta a b c d e f ≠ 0) :
    LinearIndependent K (linearQuadricProducts (scaledBaseLocusQuadricPolynomials a b c d e f)) := by
  rw [Fintype.linearIndependent_iff]
  intro q hq ij
  have hrel : scaledNetLinearRelation a b c d e f q := hq
  have hu1 := scaledNet_coeff_u1 a b c d e f q ha hb hrel
  have hu2 := scaledNet_coeff_u2 a b c d e f q ha hb hrel
  have hv1 := scaledNet_coeff_v1 a b c d e f q ha hc hrel
  have hv3 := scaledNet_coeff_v3 a b c d e f q ha hc hrel
  have hw2 := scaledNet_coeff_w2 a b c d e f q hb hc hrel
  have hw3 := scaledNet_coeff_w3 a b c d e f q hb hc hrel
  have hE := scaledNet_coeff_E a b c d e f q hrel
  have hF := scaledNet_coeff_F a b c d e f q hrel
  have hA := scaledNet_coeff_A a b c d e f q hrel hu1 hu2 hv1 hv3 hw2 hw3
  have hB := scaledNet_coeff_B a b c d e f q hrel hu1 hu2 hv1 hv3 hw2 hw3
  have hC := scaledNet_coeff_C a b c d e f q hrel hu1 hu2 hv1 hv3 hw2 hw3
  have hD := scaledNet_coeff_D a b c d e f q hrel hu1 hu2 hv1 hv3 hw2 hw3
  obtain ⟨hu0, hv0, hw0, hu3, hv2, hw1⟩ := scaled_net_remaining_coefficients_zero
    a b c d e f (q (0, 0)) (q (1, 0)) (q (2, 0))
    (q (0, 3)) (q (1, 2)) (q (2, 1)) ha hb hc hd he hf hdelta
    hE hF hA (by linear_combination hB) (by linear_combination hC) hD
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> assumption

/-- Every cubic through the four nondegenerate tangent double points lies in
the ideal of the displayed finite net of three quadrics. -/
theorem cubic_mem_scaledBaseLocus_ideal_of_nonexceptional_tangent_vanishing
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (hdelta : baseLocusDelta a b c d e f ≠ 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections a b c d e f) i) F = 0) :
    F ∈ Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) :=
  cubic_mem_scaledBaseLocus_ideal_of_tangent_vanishing a b c d e f ha hb hc
    (scaledBaseLocus_linearProducts_independent a b c d e f ha hb hc hd he hf hdelta)
    F hF hvan

end
end QuarticNet
end PfaffianDescent

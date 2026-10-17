import PfaffianDescent.QuarticFourCycleNet

/-!
# Product independence in the four-cycle branch
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

section
variable {K : Type*} [Field K]

private def fourCycleLinearRelation (b c d e : K) (q : Fin 3 × Fin 4 → K) : Prop :=
  ∑ ij, q ij • linearQuadricProducts (fourCycleScaledQuadricPolynomials b c d e) ij = 0

private theorem fourCycle_coeff_w0 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hq : fourCycleLinearRelation b c d e q) : q (2, 0) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 2 + Finsupp.single 2 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, hc, hd, he] using h

private theorem fourCycle_coeff_w1 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hb : b ≠ 0) (hc : c ≠ 0) (he : e ≠ 0)
    (hq : fourCycleLinearRelation b c d e q) : q (2, 1) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 1 2 + Finsupp.single 2 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, hb, hc, he] using h

private theorem fourCycle_coeff_w2 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hq : fourCycleLinearRelation b c d e q) : q (2, 2) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 2 2)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, hc, hd, he] using h

private theorem fourCycle_coeff_w3 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hb : b ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hq : fourCycleLinearRelation b c d e q) : q (2, 3) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 3 2)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, hb, hd, he] using h

private theorem fourCycle_coeff_u0 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hq : fourCycleLinearRelation b c d e q) : q (0, 0) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 2 + Finsupp.single 1 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply] using h

private theorem fourCycle_coeff_u1 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hq : fourCycleLinearRelation b c d e q) : q (0, 1) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 1 2)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply] using h

private theorem fourCycle_coeff_v2 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hq : fourCycleLinearRelation b c d e q) : q (1, 2) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 2 2 + Finsupp.single 3 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply] using h

private theorem fourCycle_coeff_v3 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hq : fourCycleLinearRelation b c d e q) : q (1, 3) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 2 1 + Finsupp.single 3 2)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply] using h


private theorem fourCycle_coeff_u2 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hq : fourCycleLinearRelation b c d e q)
    (hw0 : q (2, 0) = 0) (hw1 : q (2, 1) = 0)
    (hw2 : q (2, 2) = 0) (hw3 : q (2, 3) = 0) :
    q (0, 2) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, hw0, hw1, hw2, hw3] using h


private theorem fourCycle_coeff_u3 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hq : fourCycleLinearRelation b c d e q)
    (hw0 : q (2, 0) = 0) (hw1 : q (2, 1) = 0)
    (hw2 : q (2, 2) = 0) (hw3 : q (2, 3) = 0) :
    q (0, 3) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 3 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, hw0, hw1, hw2, hw3] using h


private theorem fourCycle_coeff_v0 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hq : fourCycleLinearRelation b c d e q)
    (hw0 : q (2, 0) = 0) (hw1 : q (2, 1) = 0)
    (hw2 : q (2, 2) = 0) (hw3 : q (2, 3) = 0) :
    q (1, 0) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 2 1 + Finsupp.single 3 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, hw0, hw1, hw2, hw3] using h


private theorem fourCycle_coeff_v1 (b c d e : K) (q : Fin 3 × Fin 4 → K)
    (hq : fourCycleLinearRelation b c d e q)
    (hw0 : q (2, 0) = 0) (hw1 : q (2, 1) = 0)
    (hw2 : q (2, 2) = 0) (hw3 : q (2, 3) = 0) :
    q (1, 1) = 0 := by
  unfold fourCycleLinearRelation at hq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_four,
    linearQuadricProducts, fourCycleScaledQuadricPolynomials,
    fourCycleScaledQuadrics, offDiagonalQuadric] at hq
  have h := congrArg (coeff (Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 3 1)) hq
  simpa +decide [coeff_smul, X, C_mul', add_mul, mul_add, monomial_mul, coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply, hw0, hw1, hw2, hw3] using h

/-- The twelve products of the four-cycle net with the coordinate linear
forms are independent. -/
theorem fourCycleScaled_linearProducts_independent (b c d e : K)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    LinearIndependent K (linearQuadricProducts (fourCycleScaledQuadricPolynomials b c d e)) := by
  rw [Fintype.linearIndependent_iff]
  intro q hq ij
  have hrel : fourCycleLinearRelation b c d e q := hq
  have hw0 := fourCycle_coeff_w0 b c d e q hc hd he hrel
  have hw1 := fourCycle_coeff_w1 b c d e q hb hc he hrel
  have hw2 := fourCycle_coeff_w2 b c d e q hc hd he hrel
  have hw3 := fourCycle_coeff_w3 b c d e q hb hd he hrel
  have hu0 := fourCycle_coeff_u0 b c d e q hrel
  have hu1 := fourCycle_coeff_u1 b c d e q hrel
  have hv2 := fourCycle_coeff_v2 b c d e q hrel
  have hv3 := fourCycle_coeff_v3 b c d e q hrel
  have hu2 := fourCycle_coeff_u2 b c d e q hrel hw0 hw1 hw2 hw3
  have hu3 := fourCycle_coeff_u3 b c d e q hrel hw0 hw1 hw2 hw3
  have hv0 := fourCycle_coeff_v0 b c d e q hrel hw0 hw1 hw2 hw3
  have hv1 := fourCycle_coeff_v1 b c d e q hrel hw0 hw1 hw2 hw3
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> assumption

/-- Every cubic through the four-cycle tangent double points belongs to the
ideal of the three four-cycle quadrics. -/
theorem cubic_mem_fourCycleScaled_ideal_of_nonzero_tangent_vanishing
    (b c d e : K) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections 0 b c d e 0) i) F = 0) :
    F ∈ Ideal.span (Set.range (fourCycleScaledQuadricPolynomials b c d e)) :=
  cubic_mem_fourCycleScaled_ideal_of_tangent_vanishing b c d e hb hc hd
    (fourCycleScaled_linearProducts_independent b c d e hb hc hd he) F hF hvan

end
end QuarticNet
end PfaffianDescent

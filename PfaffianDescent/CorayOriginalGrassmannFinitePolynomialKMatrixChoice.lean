import Mathlib.Algebra.MvPolynomial.Funext
import PfaffianDescent.GrassmannianChartEvaluation

/-! SOURCE ONLY. ORIGINAL-K graph matrices avoiding an honest finite family
of nonzero original parameter polynomials. This does not produce nonzero
geometric chart/q0/denominator/badimage guards. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open scoped BigOperators
universe u
variable {K : Type u} [Field K] [Infinite K]

private theorem originalKGraphParameter_nonzeroPolynomial_has_nonzero_value001
    (q : GrassmannianChartRing K 2 2) (hq : q ≠ 0) :
    ∃ x : Fin 2 × Fin 2 → K, MvPolynomial.eval x q ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hq
  apply MvPolynomial.funext
  intro x
  simpa using h x

/-- A finite family of actual individually nonzero ORIGINAL-K polynomials
in one fixed graph chart gives an ORIGINAL-K matrix avoiding every factor.
It supplies no bad-locus polynomial or geometric nonvanishing premise. -/
theorem originalGrassmannChart_exists_KMatrix_avoiding_finite_nonzero_polynomials001
    {ι : Type*} [Finite ι] (Q : ι → GrassmannianChartRing K 2 2)
    (hQ : ∀ i, Q i ≠ 0) :
    ∃ T : Matrix (Fin 2) (Fin 2) K,
      ∀ i, MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2) (Q i) ≠ 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let P : GrassmannianChartRing K 2 2 := ∏ i, Q i
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hQ i)
  obtain ⟨x, hx⟩ := originalKGraphParameter_nonzeroPolynomial_has_nonzero_value001 P hP
  have hProduct : (∏ i, MvPolynomial.eval x (Q i)) ≠ 0 := by
    simpa only [P, map_prod] using hx
  let T : Matrix (Fin 2) (Fin 2) K := fun i j => x (i, j)
  refine ⟨T, ?_⟩
  intro i
  change MvPolynomial.eval x (Q i) ≠ 0
  exact Finset.prod_ne_zero_iff.mp hProduct i (Finset.mem_univ i)

end PfaffianDescent.Coray

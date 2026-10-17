import AllCharacteristics.UnirationalityCycle

/-!
# Simultaneous avoidance of finitely many polynomial bad loci

The transverse four-line construction will have five bad equations in its
coordinate-change parameters: the determinant and four cubic line
discriminants.  Over an infinite field, once each equation is known to be a
nonzero polynomial, one parameter value avoids all of them simultaneously.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u v w

/-- Finitely many nonzero multivariable polynomials over an infinite field
are simultaneously nonzero at one rational parameter value. -/
theorem exists_mvPolynomial_eval_ne_zero_forall_of_finite
    {K : Type u} {σ : Type v} {ι : Type w}
    [Field K] [Infinite K] [Finite σ]
    [Fintype ι] (f : ι → MvPolynomial σ K)
    (hf : ∀ i, f i ≠ 0) :
    ∃ a : σ → K, ∀ i, MvPolynomial.eval a (f i) ≠ 0 := by
  classical
  have hprod : ∏ i, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hf i
  obtain ⟨a, ha⟩ :=
    exists_mvPolynomial_eval_ne_zero_of_infinite (∏ i, f i) hprod
  refine ⟨a, ?_⟩
  intro i hi
  apply ha
  rw [MvPolynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- A separately specified determinant polynomial and a finite family of bad
polynomials can be avoided by one common parameter value. -/
theorem exists_mvPolynomial_eval_det_and_family_ne_zero
    {K : Type u} {σ : Type v} {ι : Type w}
    [Field K] [Infinite K] [Finite σ]
    [Fintype ι] (det : MvPolynomial σ K)
    (f : ι → MvPolynomial σ K) (hdet : det ≠ 0)
    (hf : ∀ i, f i ≠ 0) :
    ∃ a : σ → K,
      MvPolynomial.eval a det ≠ 0 ∧
        ∀ i, MvPolynomial.eval a (f i) ≠ 0 := by
  let g : Option ι → MvPolynomial σ K
    | none => det
    | some i => f i
  have hg : ∀ i, g i ≠ 0 := by
    intro i
    cases i with
    | none => exact hdet
    | some i => exact hf i
  obtain ⟨a, ha⟩ :=
    exists_mvPolynomial_eval_ne_zero_forall_of_finite g hg
  exact ⟨a, ha none, fun i => ha (some i)⟩

end PfaffianDescent

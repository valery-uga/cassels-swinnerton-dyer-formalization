import Mathlib.Algebra.MvPolynomial.Funext

/-! # Native polynomial avoidance on the infinite ground-field grid -/
noncomputable section
namespace PfaffianDescent
universe u

theorem serreIncidencePolynomial_exists_ground_nonzero
    {K E : Type u} [Field K] [Field E] [Algebra K E] [Infinite K]
    {σ : Type u} (p : MvPolynomial σ E) (hp : p ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval (fun i => algebraMap K E (x i)) p ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hp
  apply MvPolynomial.funext_set (fun _ : σ => Set.range (algebraMap K E))
    (fun _ => Set.infinite_range_of_injective (FaithfulSMul.algebraMap_injective K E))
  intro x hx
  have hi : ∀ i, ∃ y : K, algebraMap K E y = x i := by
    intro i
    exact hx i (Set.mem_univ i)
  choose y hy using hi
  have he : (fun i => algebraMap K E (y i)) = x := funext hy
  rw [map_zero, ← he]
  exact h y

end PfaffianDescent

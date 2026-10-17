import PfaffianDescent.QuarticConjugateCoordinates
import PfaffianDescent.MatchingGeneratedFieldFixedCoefficients

/-! SOURCE ONLY, UNVERIFIED. The actual edge projector is independent of
ordering the two endpoints. Its coefficients are fixed by the actual
edge-sum stabilizer, without assuming a line field-of-definition certificate. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
open scoped BigOperators
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

def matchingEdgeProjectorMatrix (B : Basis (Fin 4) K (Fin 4 → K)) :
    Matrix (Fin 4) (Fin 4) K :=
  fun m n => B 0 m * B.repr (Pi.single n 1) 0 +
    B 1 m * B.repr (Pi.single n 1) 1

theorem permutedBasis_repr_covariance
    (B : Basis (Fin 4) K (Fin 4 → K)) (g : K ≃ₐ[k] K)
    (rho : Equiv.Perm (Fin 4))
    (hB : ∀ i m, g (B i m) = B (rho i) m)
    (w : Fin 4 → K) (j : Fin 4) :
    B.repr (fun m => g (w m)) (rho j) = g (B.repr w j) := by
  classical
  have hexp : (fun m => g (w m)) = ∑ i, g (B.repr w i) • B (rho i) := by
    funext m
    have h := congrArg (fun z : Fin 4 → K => g (z m)) (B.sum_repr w)
    simpa [Pi.smul_apply, Finset.sum_apply, map_sum, map_mul,
      smul_eq_mul, hB] using h.symm
  rw [hexp, map_sum, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

theorem edgeSum_fixed_imp_endpoint_pair
    (B : Basis (Fin 4) K (Fin 4 → K)) (g : K ≃ₐ[k] K)
    (rho : Equiv.Perm (Fin 4))
    (hB : ∀ i m, g (B i m) = B (rho i) m)
    (hx : ∀ m, g (B 0 m + B 1 m) = B 0 m + B 1 m) :
    (rho 0 = 0 ∧ rho 1 = 1) ∨ (rho 0 = 1 ∧ rho 1 = 0) := by
  classical
  have he : B (rho 0) + B (rho 1) = B 0 + B 1 := by
    funext m
    simpa only [Pi.add_apply, map_add, hB] using hx m
  have he0 := congrArg (fun w : Fin 4 → K => B.repr w 0) he
  have he1 := congrArg (fun w : Fin 4 → K => B.repr w 1) he
  simp only [map_add, Finsupp.add_apply, Basis.repr_self_apply] at he0 he1
  have hne : rho 0 ≠ rho 1 := rho.injective.ne (by decide)
  generalize h0 : rho 0 = i0 at he0 he1 hne ⊢
  generalize h1 : rho 1 = i1 at he0 he1 hne ⊢
  fin_cases i0 <;> fin_cases i1 <;>
    simp_all [map_add, Finsupp.add_apply, Basis.repr_self_apply]

theorem matchingEdgeProjectorMatrix_fixed
    (B : Basis (Fin 4) K (Fin 4 → K)) (g : K ≃ₐ[k] K)
    (rho : Equiv.Perm (Fin 4))
    (hB : ∀ i m, g (B i m) = B (rho i) m)
    (hx : ∀ m, g (B 0 m + B 1 m) = B 0 m + B 1 m)
    (m n : Fin 4) :
    g (matchingEdgeProjectorMatrix B m n) = matchingEdgeProjectorMatrix B m n := by
  classical
  have hstd : (fun j : Fin 4 => g ((Pi.single n (1 : K) : Fin 4 → K) j)) =
      (Pi.single n (1 : K) : Fin 4 → K) := by
    funext j
    by_cases h : n = j <;> simp [Pi.single_apply, h]
  have hr (i : Fin 4) : g (B.repr (Pi.single n 1) i) =
      B.repr (Pi.single n 1) (rho i) := by
    simpa only [hstd] using
      (permutedBasis_repr_covariance B g rho hB (Pi.single n 1) i).symm
  rcases edgeSum_fixed_imp_endpoint_pair B g rho hB hx with h | h
  · simp only [matchingEdgeProjectorMatrix, map_add, map_mul, hB, hr, h.1, h.2]
  · simp only [matchingEdgeProjectorMatrix, map_add, map_mul, hB, hr, h.1, h.2]
    exact add_comm _ _

end PfaffianDescent.QuarticNet

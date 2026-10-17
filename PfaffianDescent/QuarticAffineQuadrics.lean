import PfaffianDescent.QuarticInfinitesimalPoints
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Affine quadrics through a degree-four point

The ten affine monomials obtained by dehomogenizing quadrics in four
variables.  A degree-four point whose coordinates form a basis imposes four
independent conditions, leaving the six-dimensional space used in the
length-eight construction.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

universe u

noncomputable def affineQuadricExponent : Fin 10 → (Fin 3 →₀ ℕ) :=
  ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 2 1,
    Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1,
    Finsupp.single 0 1 + Finsupp.single 2 1, Finsupp.single 1 2,
    Finsupp.single 1 1 + Finsupp.single 2 1, Finsupp.single 2 2]

theorem affineQuadricExponent_injective : Function.Injective affineQuadricExponent := by
  intro i j h
  have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) h
  have h1 := congrArg (fun f : Fin 3 →₀ ℕ => f 1) h
  have h2 := congrArg (fun f : Fin 3 →₀ ℕ => f 2) h
  fin_cases i <;> fin_cases j
  all_goals solve
    | rfl
    | norm_num [affineQuadricExponent, Finsupp.single_apply, Fin.ext_iff] at h0
    | norm_num [affineQuadricExponent, Finsupp.single_apply, Fin.ext_iff] at h1
    | norm_num [affineQuadricExponent, Finsupp.single_apply, Fin.ext_iff] at h2

section

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

noncomputable def affineQuadrics : (Fin 10 → k) →ₗ[k] AffineThreeRing k :=
  Fintype.linearCombination k (fun i => monomial (affineQuadricExponent i) 1)

theorem affineQuadrics_coeff (q : Fin 10 → k) (i : Fin 10) :
    coeff (affineQuadricExponent i) (affineQuadrics q) = q i := by
  simp [affineQuadrics, Fintype.linearCombination_apply, coeff_sum, coeff_smul,
    coeff_monomial, affineQuadricExponent_injective.eq_iff]

theorem affineQuadrics_injective : Function.Injective (affineQuadrics (k := k)) := by
  intro q r h
  funext i
  simpa only [affineQuadrics_coeff] using congrArg (coeff (affineQuadricExponent i)) h

noncomputable def affineQuadricEvaluation (p : Fin 3 → L) : (Fin 10 → k) →ₗ[k] L :=
  (MvPolynomial.aeval p).toLinearMap.comp affineQuadrics

noncomputable def affineQuadricsThroughPoint (p : Fin 3 → L) : Submodule k (Fin 10 → k) :=
  LinearMap.ker (affineQuadricEvaluation (k := k) p)

theorem affineQuadricEvaluation_surjective (b : Basis (Fin 4) k L) (hb : b 0 = 1) :
    Function.Surjective (affineQuadricEvaluation (k := k) (fun i : Fin 3 => b i.succ)) := by
  intro a
  refine ⟨![b.repr a 0, b.repr a 1, b.repr a 2, b.repr a 3, 0, 0, 0, 0, 0, 0], ?_⟩
  have h := b.sum_repr a
  simpa [affineQuadricEvaluation, affineQuadrics, Fintype.linearCombination_apply,
    affineQuadricExponent, Fin.sum_univ_succ, smul_eq_mul, hb, aeval_monomial,
    Finsupp.prod_single_index, Algebra.smul_def] using h

theorem affineResidueEvaluation_surjective (b : Basis (Fin 4) k L) (hb : b 0 = 1) :
    Function.Surjective
      (MvPolynomial.aeval (fun i : Fin 3 => b i.succ) : AffineThreeRing k →ₐ[k] L) := by
  intro a
  obtain ⟨q, hq⟩ := affineQuadricEvaluation_surjective b hb a
  exact ⟨affineQuadrics q, hq⟩

theorem affineQuadricsThroughPoint_finrank (b : Basis (Fin 4) k L) (hb : b 0 = 1) :
    Module.finrank k (affineQuadricsThroughPoint (k := k) (fun i : Fin 3 => b i.succ)) = 6 := by
  have h := (affineQuadricEvaluation (k := k) (fun i : Fin 3 => b i.succ)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (affineQuadricEvaluation_surjective b hb), finrank_top] at h
  have hbL : Module.finrank k L = 4 := by simpa using finrank_eq_card_basis b
  simp only [hbL, Module.finrank_pi, finrank_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at h
  change Module.finrank k
    (LinearMap.ker (affineQuadricEvaluation (k := k) (fun i : Fin 3 => b i.succ))) = 6
  omega

end
end QuarticNet
end PfaffianDescent

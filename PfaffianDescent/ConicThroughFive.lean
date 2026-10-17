import PfaffianDescent.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PfaffianDescent
open Module
open scoped BigOperators

/-- The six monomial exponents of a plane conic. -/
noncomputable def conicExponent : Fin 6 → (Fin 3 →₀ ℕ) :=
  ![Finsupp.single 0 2, Finsupp.single 1 2, Finsupp.single 2 2,
    Finsupp.single 0 1 + Finsupp.single 1 1,
    Finsupp.single 0 1 + Finsupp.single 2 1,
    Finsupp.single 1 1 + Finsupp.single 2 1]

lemma conicExponent_injective : Function.Injective conicExponent := by
  intro i j h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  have h2 := DFunLike.congr_fun h 2
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  fin_cases i <;> fin_cases j <;>
    simp [conicExponent, Finsupp.single_apply, h01, h02, h12,
      Ne.symm h01, Ne.symm h02, Ne.symm h12] at h0 h1 h2 ⊢

lemma conicExponent_degree (i : Fin 6) : (conicExponent i).degree = 2 := by
  fin_cases i <;> norm_num [conicExponent, map_add, Finsupp.degree_single]

section
variable {K : Type*} [Field K]

noncomputable def conicPolynomial : (Fin 6 → K) →ₗ[K] MvPolynomial (Fin 3) K :=
  Fintype.linearCombination K (fun i => MvPolynomial.monomial (conicExponent i) 1)

lemma conicPolynomial_injective : Function.Injective (conicPolynomial (K := K)) := by
  apply LinearIndependent.fintypeLinearCombination_injective
  exact (MvPolynomial.basisMonomials (Fin 3) K).linearIndependent.comp
    conicExponent conicExponent_injective

lemma conicPolynomial_homogeneous (c : Fin 6 → K) : (conicPolynomial c).IsHomogeneous 2 := by
  change (∑ i : Fin 6, c i • MvPolynomial.monomial (conicExponent i) (1 : K)) ∈
    MvPolynomial.homogeneousSubmodule (Fin 3) K 2
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact MvPolynomial.isHomogeneous_monomial 1 (conicExponent_degree i)

/-- Six conic coefficients impose at most five independent evaluation conditions.
Consequently a nonzero conic through a degree-five plane point exists over the
ground field. The statement also applies to a length-five finite algebra. -/
theorem exists_conic_through_degree_five {A : Type*} [CommRing A] [Algebra K A]
    [FiniteDimensional K A] (hdim : finrank K A = 5) (p : Vec A 3) :
    ∃ q : MvPolynomial (Fin 3) K,
      q ≠ 0 ∧ q.IsHomogeneous 2 ∧ MvPolynomial.eval₂ (algebraMap K A) p q = 0 := by
  let E : (Fin 6 → K) →ₗ[K] A := (MvPolynomial.aeval p).toLinearMap.comp conicPolynomial
  have hker : LinearMap.ker E ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa [hdim])
  obtain ⟨c, hc, hcnz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨conicPolynomial c, ?_, conicPolynomial_homogeneous c, hc⟩
  intro h
  apply hcnz
  apply conicPolynomial_injective
  exact h.trans (map_zero conicPolynomial).symm

end
end PfaffianDescent

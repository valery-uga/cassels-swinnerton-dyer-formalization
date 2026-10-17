import PfaffianDescent.Basic
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K A L ι : Type*} [Field K] [Infinite K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] [Fintype ι]

/-- A finite collection of distinct algebra homomorphisms is separated by one algebra element
when the ground field is infinite. -/
theorem exists_separating_element (f : ι → A →ₐ[K] L) (hf : Function.Injective f) :
    ∃ a : A, Function.Injective (fun i => f i a) := by
  classical
  let J := {p : ι × ι // p.1 ≠ p.2}
  let D : J → A →ₗ[K] L := fun p => (f p.val.1).toLinearMap - (f p.val.2).toLinearMap
  have hker : ∀ j : J, LinearMap.ker (D j) ≠ ⊤ := by
    intro j htop
    have hzero : D j = 0 := LinearMap.ker_eq_top.mp htop
    apply j.property
    apply hf
    ext a
    have h := LinearMap.congr_fun hzero a
    change f j.val.1 a - f j.val.2 a = 0 at h
    exact sub_eq_zero.mp h
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun j : J => LinearMap.ker (D j)) hker
  refine ⟨a, ?_⟩
  intro i j hij
  by_contra hne
  apply ha ⟨(i,j),hne⟩
  change f i a - f j a = 0
  exact sub_eq_zero.mpr hij

end

section
variable {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] {n : ℕ}

/-- Distinct geometric evaluations of one element make its first `n` powers independent. -/
theorem powers_independent_of_separated_homs (f : Fin n → A →ₐ[K] L) (a : A)
    (ha : Function.Injective (fun i => f i a)) :
    LinearIndependent K (fun i : Fin n => a^(i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he (j : Fin n) : ∑ k : Fin n, algebraMap K L (c k) * (f j a)^(k : ℕ) = 0 := by
    have h := congrArg (f j) hc
    simpa only [map_sum, map_smul, map_pow, map_zero, Algebra.smul_def, map_mul, AlgHom.commutes] using h
  have hz : (fun i : Fin n => algebraMap K L (c i)) = 0 :=
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero ha he
  apply (algebraMap K L).injective
  simpa only [map_zero, Pi.zero_apply] using congrFun hz i

/-- A finite algebra of dimension `n` with `n` distinct geometric evaluations is monogenic.
The power basis is constructed over the original field. -/
theorem exists_power_basis_of_distinct_homs [Infinite K] [FiniteDimensional K A]
    (hdim : finrank K A = n) (f : Fin n → A →ₐ[K] L) (hf : Function.Injective f) :
    ∃ a : A, ∃ b : Basis (Fin n) K A, ∀ i, b i = a^(i : ℕ) := by
  obtain ⟨a, ha⟩ := exists_separating_element f hf
  have hli := powers_independent_of_separated_homs f a ha
  have hcard : Fintype.card (Fin n) = finrank K A := by rw [Fintype.card_fin, hdim]
  refine ⟨a, basisOfLinearIndependentOfCardEqFinrank' _ hli hcard, ?_⟩
  intro i
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (fun i : Fin n => a^(i : ℕ)) hli hcard) i

end
end PfaffianDescent

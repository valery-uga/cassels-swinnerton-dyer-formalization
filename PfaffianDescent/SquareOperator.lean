import PfaffianDescent.Isotropic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

namespace PfaffianDescent
open Module
open _root_.LinearMap (BilinForm)
open scoped BigOperators

section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

/-- The two eigenspaces of an operator squaring to a nonzero square span the space. -/
theorem eigenspaces_span_of_square (f : V →ₗ[K] V) (r : K) (hr : 2*r ≠ 0)
    (hsq : ∀ v, f (f v) = r^2 • v) : Module.End.eigenspace f r ⊔ Module.End.eigenspace f (-r) = ⊤ := by
  apply top_unique
  intro v _
  have hp : f v + r • v ∈ Module.End.eigenspace f r := by
    rw [Module.End.mem_eigenspace_iff]
    simp only [map_add, map_smul, hsq]
    module
  have hm : f v - r • v ∈ Module.End.eigenspace f (-r) := by
    rw [Module.End.mem_eigenspace_iff]
    simp only [map_sub, map_smul, hsq]
    module
  let U := Module.End.eigenspace f r ⊔ Module.End.eigenspace f (-r)
  have hsub : (f v + r • v) - (f v - r • v) ∈ U :=
    U.sub_mem (show _ ∈ U from (le_sup_left : Module.End.eigenspace f r ≤ U) hp) (show _ ∈ U from (le_sup_right : Module.End.eigenspace f (-r) ≤ U) hm)
  have heq : (f v + r • v) - (f v - r • v) = (2*r) • v := by module
  rw [heq] at hsub
  have hh := U.smul_mem (2*r)⁻¹ hsub
  simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using hh

omit [FiniteDimensional K V] in
/-- A subspace of dimension at least three contains a three-dimensional subspace. -/
theorem exists_three_subspace (U : Submodule K V) (hU : 3 ≤ finrank K U) :
    ∃ W : Submodule K V, W ≤ U ∧ finrank K W = 3 := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hU
  let w : Fin 3 → V := fun i => (v i : V)
  have hw : LinearIndependent K w := hv.map' U.subtype (LinearMap.ker_eq_bot.mpr U.subtype_injective)
  refine ⟨Submodule.span K (Set.range w), ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (v i).property
  · simpa only [Fintype.card_fin] using finrank_span_eq_card hw

omit [FiniteDimensional K V] in
/-- An eigen-subspace of an anti-self-adjoint operator is isotropic at a nonzero eigenvalue. -/
theorem isotropic_eigenspace (B : BilinForm K V) (f : V →ₗ[K] V) (r : K)
    (hr : 2*r ≠ 0) (hcomp : ∀ v w, B (f v) w + B v (f w) = 0)
    (v w : Module.End.eigenspace f r) : B v w = 0 := by
  have hv := Module.End.mem_eigenspace_iff.mp v.property
  have hw := Module.End.mem_eigenspace_iff.mp w.property
  have hh := hcomp v w
  rw [hv, hw] at hh
  simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at hh
  have hz : (2*r) * B v w = 0 := by linear_combination hh
  exact (mul_eq_zero.mp hz).resolve_left hr

/-- A square operator compatible with three forms supplies a common isotropic three-space. -/
theorem common_isotropic_of_square (hdim : finrank K V = 6)
    (B : Fin 3 → BilinForm K V) (f : V →ₗ[K] V) (r : K)
    (hr : 2*r ≠ 0) (hsq : ∀ v, f (f v) = r^2 • v)
    (hcomp : ∀ i v w, B i (f v) w + B i v (f w) = 0) :
    ∃ W : Submodule K V, finrank K W = 3 ∧ ∀ i, ∀ v w : W, B i v w = 0 := by
  have hspan := eigenspaces_span_of_square f r hr hsq
  have hdimSum := Submodule.finrank_sup_add_finrank_inf_eq (Module.End.eigenspace f r) (Module.End.eigenspace f (-r))
  rw [hspan, finrank_top, hdim] at hdimSum
  have hcases : 3 ≤ finrank K (Module.End.eigenspace f r) ∨ 3 ≤ finrank K (Module.End.eigenspace f (-r)) := by omega
  rcases hcases with hp | hm
  · obtain ⟨W, hW, hdimW⟩ := exists_three_subspace (Module.End.eigenspace f r) hp
    refine ⟨W, hdimW, fun i v w => ?_⟩
    exact isotropic_eigenspace (B i) f r hr (hcomp i) ⟨v, hW v.property⟩ ⟨w, hW w.property⟩
  · obtain ⟨W, hW, hdimW⟩ := exists_three_subspace (Module.End.eigenspace f (-r)) hm
    have hneg : 2*(-r) ≠ 0 := by simpa only [mul_neg, neg_ne_zero] using hr
    refine ⟨W, hdimW, fun i v w => ?_⟩
    exact isotropic_eigenspace (B i) f (-r) hneg (hcomp i) ⟨v, hW v.property⟩ ⟨w, hW w.property⟩

end
end PfaffianDescent

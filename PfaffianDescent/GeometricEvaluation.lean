import PfaffianDescent.ProjectiveFrame
import PfaffianDescent.AlgebraFrobenius
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K : Type*} [Field K]

/-- Every coefficient of a nonzero relation on a projective frame is nonzero. -/
theorem frame_relation_coeff_ne_zero (p : Fin 5 → Vec K 4) (hp : FivePointGeneralPosition p)
    (c : Fin 5 → K) (hc : c ≠ 0) (hrel : ∑ i : Fin 5, c i • p i = 0) :
    ∀ i, c i ≠ 0 := by
  intro i hi
  have hs := hrel
  rw [Fin.sum_univ_succAbove _ i, hi, zero_smul, zero_add] at hs
  have hli := hp i.succAbove (Fin.succAbove_right_injective)
  have hz := Fintype.linearIndependent_iff.mp hli (fun j => c (i.succAbove j)) hs
  apply hc
  funext j
  by_cases hji : j = i
  · subst j
    exact hi
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    exact hz k

end

section
variable {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] [FiniteDimensional K A] {n : ℕ}

/-- With as many geometric evaluations as the algebra dimension, the evaluations form
an extension-field basis of all ground-field linear maps into that field. -/
noncomputable def algebraHomsBasis (hdim : finrank K A = n)
    (f : Fin n → A →ₐ[K] L) (hf : Function.Injective f) : Basis (Fin n) L (A →ₗ[K] L) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun i => (f i).toLinearMap)
    ((linearIndependent_algHom_toLinearMap K A L).comp f hf)
    (by rw [Fintype.card_fin, Module.finrank_linearMap_self, hdim])

theorem algebraHomsBasis_apply (hdim : finrank K A = n)
    (f : Fin n → A →ₐ[K] L) (hf : Function.Injective f) (i : Fin n) :
    algebraHomsBasis hdim f hf i = (f i).toLinearMap := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i

/-- An element annihilated by every geometric evaluation is zero. -/
theorem eq_zero_of_all_geometric_evaluations (hdim : finrank K A = n)
    (f : Fin n → A →ₐ[K] L) (hf : Function.Injective f) (a : A) (ha : ∀ i, f i a = 0) : a = 0 := by
  let B := algebraHomsBasis hdim f hf
  have hg (g : A →ₗ[K] L) : g a = 0 := by
    have h := congrArg (fun h : A →ₗ[K] L => h a) (B.sum_repr g)
    simp only [B, LinearMap.sum_apply, LinearMap.smul_apply, algebraHomsBasis_apply,
      AlgHom.toLinearMap_apply, ha, smul_zero, Finset.sum_const_zero] at h
    exact h.symm
  apply (Module.forall_dual_apply_eq_zero_iff K a).mp
  intro ell
  apply (algebraMap K L).injective
  have he := hg ((Algebra.linearMap K L).comp ell)
  simpa only [LinearMap.comp_apply, Algebra.linearMap_apply, map_zero] using he

end
end PfaffianDescent

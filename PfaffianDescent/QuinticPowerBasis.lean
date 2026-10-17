import PfaffianDescent.FieldHyperplanes
import PfaffianDescent.Basic
import Mathlib.FieldTheory.PrimitiveElement

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- The primitive element theorem, with the basis indexed by exactly five entries. -/
theorem exists_power_basis_five (hdim : finrank K L = 5) :
    ∃ α : L, ∃ b : Basis (Fin 5) K L, ∀ i, b i = α ^ (i : ℕ) := by
  let p := Field.powerBasisOfFiniteOfSeparable K L
  have he : p.dim = 5 := p.finrank.symm.trans hdim
  refine ⟨p.gen, p.basis.reindex (finCongr he), ?_⟩
  intro i
  rw [Basis.reindex_apply, p.basis_eq_pow]
  rfl

/-- The coefficients of the monic quintic relation are ground-field scalars. -/
theorem quintic_relation_of_power_basis (α : L) (b : Basis (Fin 5) K L)
    (hb : ∀ i, b i = α ^ (i : ℕ)) :
    ∃ a : Vec K 5, α^5 + ∑ i : Fin 5, algebraMap K L (a i) * α^(i : ℕ) = 0 := by
  refine ⟨fun i => -b.repr (α^5) i, ?_⟩
  have h := b.sum_repr (α^5)
  simp only [hb, Algebra.smul_def] at h
  simp only [map_neg, neg_mul, Finset.sum_neg_distrib, h, add_neg_cancel]

/-- A hyperplane in a degree-five field is a scalar multiple of the first four powers
of a primitive element. This works over the ground field without labeling conjugates. -/
theorem quintic_hyperplane_normal_form (hdim : finrank K L = 5)
    (W : Submodule K L) (hW : finrank K W = 4) :
    ∃ α : L, ∃ b : Basis (Fin 5) K L, (∀ i, b i = α^(i : ℕ)) ∧
      ∃ v : L, v ≠ 0 ∧
        Submodule.span K (Set.range (fun i : Fin 4 => v * α^(i : ℕ))) = W := by
  obtain ⟨α, b, hb⟩ := exists_power_basis_five hdim
  let q : Fin 4 → L := fun i => α^(i : ℕ)
  have hq : LinearIndependent K q := by
    have h := b.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective 4)
    simpa only [Function.comp_def, hb, Fin.val_castSucc] using h
  let H := Submodule.span K (Set.range q)
  have hH : finrank K H = 4 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hq
  obtain ⟨v, hv, hmem⟩ := field_hyperplanes_multiplicative W H (by omega) (by omega)
  refine ⟨α, b, hb, v, hv, ?_⟩
  let U := Submodule.span K (Set.range (fun i : Fin 4 => v * q i))
  have hle : U ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (hmem (q i)).mpr (Submodule.subset_span (Set.mem_range_self i))
  have hi : LinearIndependent K (fun i : Fin 4 => v * q i) := by
    exact hq.map' (LinearMap.mulLeft K v) (by
      rw [LinearMap.ker_eq_bot]
      intro a b h
      exact mul_left_cancel₀ hv h)
  have hU : finrank K U = 4 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hi
  exact Submodule.eq_of_le_of_finrank_eq hle (hU.trans hW.symm)

end
end PfaffianDescent

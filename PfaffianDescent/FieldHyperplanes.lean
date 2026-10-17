import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Multiplication acts transitively on hyperplanes in a finite field extension.
This supplies the coordinate normalization for a noncoplanar degree-five point. -/
namespace PfaffianDescent
open Module

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Translate a linear functional by multiplication in the extension field. -/
def multiplicationDual (ell : Module.Dual K L) : L →ₗ[K] Module.Dual K L where
  toFun v :=
    { toFun := fun w => ell (v * w)
      map_add' := by intro x y; rw [mul_add, map_add]
      map_smul' := by intro c x; simp only [mul_smul_comm, map_smul, RingHom.id_apply] }
  map_add' := by
    intro v w
    ext x
    change ell ((v + w) * x) = ell (v * x) + ell (w * x)
    rw [add_mul, map_add]
  map_smul' := by
    intro c v
    ext x
    change ell ((c • v) * x) = c • ell (v * x)
    rw [smul_mul_assoc, map_smul]

theorem multiplicationDual_injective (ell : Module.Dual K L) (hell : ell ≠ 0) :
    Function.Injective (multiplicationDual ell) := by
  intro v w hvw
  by_contra hne
  have hd : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hzero : multiplicationDual ell (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  apply hell
  ext x
  have h := congrArg (fun f : Module.Dual K L => f ((v - w)⁻¹ * x)) hzero
  change ell ((v - w) * ((v - w)⁻¹ * x)) = 0 at h
  rwa [← mul_assoc, mul_inv_cancel₀ hd, one_mul] at h

theorem multiplicationDual_surjective (ell : Module.Dual K L) (hell : ell ≠ 0) :
    Function.Surjective (multiplicationDual ell) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show finrank K L = finrank K (Module.Dual K L) by rw [Subspace.dual_finrank_eq])).mp
  exact multiplicationDual_injective ell hell

/-- A codimension-one subspace is the kernel of a nonzero linear functional. -/
theorem hyperplane_eq_kernel (W : Submodule K L)
    (hW : finrank K W + 1 = finrank K L) :
    ∃ ell : Module.Dual K L, ell ≠ 0 ∧ W = LinearMap.ker ell := by
  have hproper : W < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro h
    rw [h, finrank_top] at hW
    omega
  obtain ⟨ell, hell, hmap⟩ := W.exists_dual_map_eq_bot_of_lt_top hproper inferInstance
  refine ⟨ell, hell, ?_⟩
  have hle : W ≤ LinearMap.ker ell := by
    intro x hx
    have hm : ell x ∈ W.map ell := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hmap, Submodule.mem_bot] at hm
    exact hm
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hell
  omega

/-- Every pair of hyperplanes in a finite field extension differ by multiplication
by a nonzero element of that field. -/
theorem field_hyperplanes_multiplicative (W H : Submodule K L)
    (hW : finrank K W + 1 = finrank K L)
    (hH : finrank K H + 1 = finrank K L) :
    ∃ v : L, v ≠ 0 ∧ ∀ x : L, v * x ∈ W ↔ x ∈ H := by
  obtain ⟨ell, hell, hwell⟩ := hyperplane_eq_kernel W hW
  obtain ⟨psi, hpsi, hhpsi⟩ := hyperplane_eq_kernel H hH
  obtain ⟨v, hv⟩ := multiplicationDual_surjective ell hell psi
  refine ⟨v, ?_, ?_⟩
  · intro hz
    rw [hz, map_zero] at hv
    exact hpsi hv.symm
  · intro x
    rw [hwell, hhpsi]
    change ell (v * x) = 0 ↔ psi x = 0
    exact Iff.of_eq (congrArg (fun z : K => z = 0) (congrArg (fun f : Module.Dual K L => f x) hv))

end
end PfaffianDescent

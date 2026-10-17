import PfaffianDescent.CubicCoordinates
import Mathlib.LinearAlgebra.Matrix.Nonsingular

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- Noncoplanar degree-five coordinates are a ground-field invertible linear change
of rational-normal-cubic coordinates, up to one common extension-field scalar. -/
theorem independent_quintic_coordinates (hdim : finrank K L = 5)
    (p : Vec L 4) (hp : LinearIndependent K p) :
    ∃ α : L, ∃ b : Basis (Fin 5) K L, (∀ i, b i = α^(i : ℕ)) ∧
      ∃ v : L, v ≠ 0 ∧ ∃ M : Mat K 4, Function.Injective M.mulVec ∧
        p = v • (M.map (algebraMap K L)).mulVec (rationalCubicCoordinates α) := by
  let W := Submodule.span K (Set.range p)
  have hW : finrank K W = 4 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hp
  obtain ⟨α, b, hb, v, hv, hspan⟩ := quintic_hyperplane_normal_form hdim W hW
  have hmem : ∀ i, p i ∈ Submodule.span K (Set.range (fun j : Fin 4 => v * α^(j : ℕ))) := by
    intro i
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  choose M hM using fun i => (Submodule.mem_span_range_iff_exists_fun K).mp (hmem i)
  let phi : Vec K 4 →ₗ[K] L :=
    { toFun := fun d => ∑ j : Fin 4, d j • (v * α^(j : ℕ))
      map_add' := by intro x y; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro s x; simp only [Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hcomp : phi ∘ M = p := funext hM
  have hrows : LinearIndependent K M := LinearIndependent.of_comp phi (by rw [hcomp]; exact hp)
  have hinj : Function.Injective (Matrix.mulVec (M : Mat K 4)) :=
    Matrix.mulVec_injective_iff.mpr (Matrix.Nonsingular.of_linearIndependent_row hrows).linearIndependent_col
  refine ⟨α, b, hb, v, hv, M, hinj, ?_⟩
  have hpow : ∀ j : Fin 4, rationalCubicCoordinates α j = α^(j : ℕ) := by
    intro j
    fin_cases j
    · change (1 : L) = α^0
      exact (pow_zero α).symm
    · change α = α^1
      exact (pow_one α).symm
    · rfl
    · rfl
  funext i
  rw [← hM i]
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, smul_eq_mul,
    hpow, Finset.mul_sum, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _
  change algebraMap K L (M i j) * (v * α^(j : ℕ)) = v * (algebraMap K L (M i j) * α^(j : ℕ))
  ring

/-- A cubic with a noncoplanar degree-five point has a rational point.
The presentation and the coordinate change are proved over the ground field. -/
theorem cubic_descent_of_independent_quintic_point (hdim : finrank K L = 5)
    (c : Cubic K 4) (p : Vec L 4) (hp : LinearIndependent K p)
    (hF : (c.map (algebraMap K L)).eval p = 0) :
    ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  obtain ⟨α, b, hb, v, hv, M, hinj, hcoord⟩ := independent_quintic_coordinates hdim p hp
  rw [hcoord, Cubic.eval_smul] at hF
  have hz := (mul_eq_zero.mp hF).resolve_left (pow_ne_zero 3 hv)
  have hcomp : ((c.compLinear M).map (algebraMap K L)).eval (rationalCubicCoordinates α) = 0 := by
    rw [Cubic.compLinear_map, Cubic.eval_compLinear]
    exact hz
  obtain ⟨x, hx, he⟩ := canonical_quintic_tensor_descent α b hb (c.compLinear M) hcomp
  refine ⟨M.mulVec x, ?_, ?_⟩
  · intro hzero
    apply hx
    apply hinj
    simpa only [Matrix.mulVec_zero] using hzero
  · rw [← Cubic.eval_compLinear]
    exact he

end
end PfaffianDescent

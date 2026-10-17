import PfaffianDescent.QuinticFunctional
import PfaffianDescent.CubicLinear

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- Evaluation at an extension-field point, as a linear map in the cubic coefficients. -/
def cubicEvaluation (p : Vec L n) : Cubic K n →ₗ[K] L :=
  Fintype.linearCombination K (fun i => p i.1 * p i.2.1 * p i.2.2)

theorem cubicEvaluation_eq (p : Vec L n) (c : Cubic K n) :
    cubicEvaluation p c = (c.map (algebraMap K L)).eval p := by
  simp only [cubicEvaluation, Fintype.linearCombination_apply, Cubic.eval, Cubic.map, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A point lying on a ground-field line descends if its parameter has five independent powers. -/
theorem cubic_descent_of_quintic_pair (α : L) (B : Basis (Fin 5) K L)
    (hB : ∀ i, B i = α^(i : ℕ)) (c : Cubic K n) (p : Vec L n) (hp : p ≠ 0)
    (a d : Vec K n) (hcoord : ∀ i, p i = algebraMap K L (a i) + algebraMap K L (d i) * α)
    (hF : (c.map (algebraMap K L)).eval p = 0) :
    ∃ x : Vec K n, x ≠ 0 ∧ c.eval x = 0 := by
  let f := algebraMap K L
  let aL := fun i => f (a i)
  let dL := fun i => f (d i)
  have hline : p = (1 : L) • aL + α • dL := by
    funext i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, mul_comm] using hcoord i
  have hh := (c.map f).eval_line aL dL 1 α
  rw [← hline, hF] at hh
  simp only [aL, dL, Cubic.eval_map, Cubic.mixed_map, one_pow, one_mul] at hh
  let r : Vec K 5 := ![c.eval a, c.mixed a d, c.mixed d a, c.eval d, 0]
  have hr : ∑ i : Fin 5, r i • B i = 0 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change c.eval a • B 0 + (c.mixed a d • B 1 + (c.mixed d a • B 2 + (c.eval d • B 3 + 0 • B 4))) = 0
    simp only [hB, Algebra.smul_def, map_zero, zero_mul, add_zero]
    change f (c.eval a) * α^0 + (f (c.mixed a d) * α^1 +
      (f (c.mixed d a) * α^2 + f (c.eval d) * α^3)) = 0
    linear_combination -hh
  have he := Fintype.linearIndependent_iff.mp B.linearIndependent r hr
  by_cases ha : a = 0
  · refine ⟨d, ?_, he 3⟩
    intro hd
    apply hp
    funext i
    rw [hcoord i, ha, hd]
    simp only [Pi.zero_apply, map_zero, zero_mul, add_zero]
  · exact ⟨a, ha, he 0⟩

end

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {n : ℕ}

/-- Unless a rational point already follows from a ground-field line, cubic
evaluation at a normalized quintic point is surjective onto its residue field. -/
theorem quintic_cubic_evaluation_dichotomy (hdim : finrank K L = 5)
    (c : Cubic K n) (p : Vec L n) (k : Fin n) (hk : p k = 1)
    (hF : (c.map (algebraMap K L)).eval p = 0) :
    (∃ x : Vec K n, x ≠ 0 ∧ c.eval x = 0) ∨ Function.Surjective (cubicEvaluation p : Cubic K n →ₗ[K] L) := by
  classical
  by_cases hsurj : Function.Surjective (cubicEvaluation p : Cubic K n →ₗ[K] L)
  · exact Or.inr hsurj
  left
  have hp : p ≠ 0 := by
    intro hz
    have h := congrFun hz k
    rw [hk] at h
    exact one_ne_zero h
  by_cases hground : ∀ i, p i ∈ (⊥ : IntermediateField K L)
  · choose a ha using fun i => (IntermediateField.mem_bot.mp (hground i))
    refine ⟨a, ?_, ?_⟩
    · intro hz
      have h := ha k
      rw [hz, Pi.zero_apply, map_zero, hk] at h
      exact zero_ne_one h
    · apply (algebraMap K L).injective
      rw [map_zero, ← Cubic.eval_map]
      rw [show (fun i => algebraMap K L (a i)) = p from funext ha]
      exact hF
  push Not at hground
  obtain ⟨j, hj⟩ := hground
  obtain ⟨B, hB⟩ := quintic_generator_basis hdim (p j) hj
  let W := LinearMap.range (cubicEvaluation p : Cubic K n →ₗ[K] L)
  have hproper : W < ⊤ := lt_top_iff_ne_top.mpr (fun h => hsurj (LinearMap.range_eq_top.mp h))
  obtain ⟨ell, hell, hwell⟩ := W.exists_dual_map_eq_bot_of_lt_top hproper inferInstance
  have hproducts : ∀ i₀ i₁ i₂, ell (p i₀ * p i₁ * p i₂) = 0 := by
    intro i₀ i₁ i₂
    have hm : p i₀ * p i₁ * p i₂ ∈ W := by
      refine ⟨Pi.single (i₀, i₁, i₂) 1, ?_⟩
      simp only [cubicEvaluation, Fintype.linearCombination_apply_single, one_smul]
    have hh : ell (p i₀ * p i₁ * p i₂) ∈ W.map ell := Submodule.mem_map.mpr ⟨_, hm, rfl⟩
    rwa [hwell, Submodule.mem_bot] at hh
  have hpow : ∀ i : Fin 4, ell ((p j)^(i : ℕ)) = 0 := by
    intro i
    fin_cases i
    · simpa only [hk, one_mul, pow_zero] using hproducts k k k
    · simpa only [hk, mul_one, pow_one] using hproducts j k k
    · simpa only [hk, mul_one, pow_two] using hproducts j j k
    · change ell ((p j)^3) = 0
      have hh : (p j)^3 = p j * p j * p j := by ring
      rw [hh]
      exact hproducts j j j
  have hpair : ∀ i, ∃ a d : K, p i = algebraMap K L a + algebraMap K L d * p j := by
    intro i
    apply quintic_functional_forces_pair (p j) B hB ell hell hpow (p i)
    · simpa only [hk, mul_one] using hproducts i k k
    · simpa only [hk, mul_one] using hproducts j i k
    · simpa only [pow_two] using hproducts j j i
  choose a d had using hpair
  exact cubic_descent_of_quintic_pair (p j) B hB c p hp a d had hF

end
end PfaffianDescent

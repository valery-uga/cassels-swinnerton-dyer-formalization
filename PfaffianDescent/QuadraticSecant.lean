import PfaffianDescent.Cubic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic.FieldSimp

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A quadratic extension admits a basis consisting of one and a generator. -/
theorem quadratic_generator [FiniteDimensional K L] (hdim : finrank K L = 2) :
    ∃ α : L,
      (∀ z : L, ∃ a b : K, z = algebraMap K L a + algebraMap K L b * α) ∧
      (∀ a b : K, algebraMap K L a + algebraMap K L b * α = 0 → a = 0 ∧ b = 0) := by
  obtain ⟨α, hα⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := K) (M := L) (by omega) (x := (1 : L)) one_ne_zero
  let b := basisOfLinearIndependentOfCardEqFinrank hα
    (show Fintype.card (Fin 2) = finrank K L by simp [hdim])
  have hb : (b : Fin 2 → L) = ![1, α] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  refine ⟨α, ?_, ?_⟩
  · intro z
    refine ⟨b.repr z 0, b.repr z 1, ?_⟩
    have hh := (b.sum_repr z).symm
    rw [Fin.sum_univ_two] at hh
    simpa only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Algebra.smul_def, mul_one] using hh
  · intro a d h
    have hh : ∑ i : Fin 2, ![a, d] i • ![(1 : L), α] i = 0 := by
      simpa [Fin.sum_univ_two, Algebra.smul_def] using h
    have he := Fintype.linearIndependent_iff.mp hα ![a, d] hh
    exact ⟨he 0, he 1⟩

/-- Quadratic secant descent, using coordinates in a quadratic basis. -/
theorem cubic_descent_of_quadratic_generator {n : ℕ} (c : Cubic K n)
    (α : L)
    (hspan : ∀ z : L, ∃ a b : K, z = algebraMap K L a + algebraMap K L b * α)
    (hind : ∀ a b : K, algebraMap K L a + algebraMap K L b * α = 0 → a = 0 ∧ b = 0)
    (x : Vec L n) (hx : x ≠ 0) (hF : (c.map (algebraMap K L)).eval x = 0) :
    ∃ y : Vec K n, y ≠ 0 ∧ c.eval y = 0 := by
  classical
  choose a b hab using fun i => hspan (x i)
  obtain ⟨r, s, hrs⟩ := hspan (α^2)
  let f := algebraMap K L
  let cL := c.map f
  have hline : x = (1 : L) • (fun i => f (a i)) + α • (fun i => f (b i)) := by
    funext i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, mul_comm] using hab i
  have hroot : f (c.eval a) + α*f (c.mixed a b) + α^2*f (c.mixed b a) +
      α^3*f (c.eval b) = 0 := by
    have hh := cL.eval_line (fun i => f (a i)) (fun i => f (b i)) 1 α
    rw [← hline, hF] at hh
    simpa only [cL, Cubic.eval_map, Cubic.mixed_map, one_pow, one_mul] using hh.symm
  have he : f (c.eval a + r*c.mixed b a + r*s*c.eval b) +
      f (c.mixed a b + s*c.mixed b a + (r+s^2)*c.eval b) * α = 0 := by
    simp only [map_add, map_mul, map_pow]
    linear_combination hroot - (f (c.mixed b a) + (α+f s)*f (c.eval b)) * hrs
  obtain ⟨h₀, h₁⟩ := hind _ _ he
  by_cases hb : b = 0
  · have hxa : x = fun i => f (a i) := by
      funext i
      simpa only [hb, Pi.zero_apply, map_zero, zero_mul, add_zero] using hab i
    refine ⟨a, ?_, ?_⟩
    · intro ha
      apply hx
      rw [hxa, ha]
      funext i
      exact map_zero f
    · apply f.injective
      rw [map_zero, ← Cubic.eval_map, ← hxa]
      exact hF
  by_cases hd : c.eval b = 0
  · exact ⟨b, hb, hd⟩
  let lam := (c.mixed b a + s*c.eval b) / c.eval b
  have hμ : f lam + α ≠ 0 := by
    intro hz
    have hh : f lam + f 1 * α = 0 := by simpa only [map_one, one_mul] using hz
    exact one_ne_zero (hind _ _ hh).2
  let q := c.eval b • a + (-(c.mixed b a + s*c.eval b)) • b
  have hq : q ≠ 0 := by
    intro hq
    have ha : a = lam • b := by
      funext i
      apply (mul_left_cancel₀ hd)
      have hi := congrFun hq i
      change c.eval b * a i + -(c.mixed b a + s*c.eval b) * b i = 0 at hi
      change c.eval b * a i = c.eval b * (lam * b i)
      dsimp [lam]
      field_simp
      linear_combination hi
    have hxx : x = (f lam + α) • (fun i => f (b i)) := by
      funext i
      rw [hab i, ha]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    rw [hxx, Cubic.eval_smul, Cubic.eval_map] at hF
    exact (mul_ne_zero (pow_ne_zero 3 hμ) ((map_ne_zero f).mpr hd)) hF
  refine ⟨q, hq, ?_⟩
  rw [show q = c.eval b • a + (-(c.mixed b a + s*c.eval b)) • b from rfl,
    Cubic.eval_line]
  exact Cubic.residual_identity _ _ _ _ r s h₀ h₁

/-- A nonzero point on a cubic over a quadratic extension descends to the base field. -/
theorem cubic_quadratic_secant [FiniteDimensional K L] (hdim : finrank K L = 2)
    {n : ℕ} (c : Cubic K n) (x : Vec L n) (hx : x ≠ 0)
    (hF : (c.map (algebraMap K L)).eval x = 0) :
    ∃ y : Vec K n, y ≠ 0 ∧ c.eval y = 0 := by
  obtain ⟨α, hspan, hind⟩ := quadratic_generator hdim
  exact cubic_descent_of_quadratic_generator c α hspan hind x hx hF

/-- The degree-at-most-two formulation, including extensions of degree one. -/
theorem cubic_degree_le_two_secant [FiniteDimensional K L]
    (hdim : finrank K L ≤ 2) {n : ℕ} (c : Cubic K n)
    (x : Vec L n) (hx : x ≠ 0) (hF : (c.map (algebraMap K L)).eval x = 0) :
    ∃ y : Vec K n, y ≠ 0 ∧ c.eval y = 0 := by
  have hpos : 0 < finrank K L := Module.finrank_pos
  have hcases : finrank K L = 1 ∨ finrank K L = 2 := by omega
  rcases hcases with h₁ | h₂
  · have hsurj := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h₁).2
    choose y hy using fun i => hsurj (x i)
    have heq : (fun i => algebraMap K L (y i)) = x := funext hy
    refine ⟨y, ?_, ?_⟩
    · intro hz
      apply hx
      rw [← heq, hz]
      funext i
      exact map_zero _
    · apply (algebraMap K L).injective
      rw [map_zero, ← Cubic.eval_map, heq]
      exact hF
  · exact cubic_quadratic_secant h₂ c x hx hF

end
end PfaffianDescent

import PfaffianDescent.AlgebraFrobenius
import PfaffianDescent.Basic
import Mathlib.LinearAlgebra.Basis.Defs

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The top-coefficient functional in a quintic power basis. -/
noncomputable def quinticPowerFunctional (b : Basis (Fin 5) K A) : Module.Dual K A := b.coord 4

theorem quinticPowerFunctional_pow (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) (i : Fin 5) :
    quinticPowerFunctional b (a^(i : ℕ)) = if i = 4 then 1 else 0 := by
  rw [← hb i]
  exact b.repr_self_apply i 4

theorem quintic_power_repr_expansion (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) (v : A) :
    v = b.repr v 0 • 1 + b.repr v 1 • a + b.repr v 2 • a^2 +
      b.repr v 3 • a^3 + b.repr v 4 • a^4 := by
  have h := b.sum_repr v
  simp only [hb, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  change b.repr v 0 • a^0 + (b.repr v 1 • a^1 + (b.repr v 2 • a^2 +
    (b.repr v 3 • a^3 + b.repr v 4 • a^4))) = v at h
  conv_lhs => rw [← h]
  simp only [pow_zero, pow_one]
  abel

/-- Top-coefficient multiplication is nondegenerate for every quintic monogenic algebra,
including algebras with zero divisors or nilpotents. -/
theorem quinticPowerFunctional_frobenius (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) : IsFrobeniusFunctional (quinticPowerFunctional b) := by
  apply (injective_iff_map_eq_zero (algebraMultiplicationDual (quinticPowerFunctional b))).mpr
  intro v hv
  have hz (w : A) : quinticPowerFunctional b (v*w) = 0 := LinearMap.congr_fun hv w
  have hrepr := quintic_power_repr_expansion a b hb v
  have he0 : quinticPowerFunctional b (1) = 0 := by
    have hh := quinticPowerFunctional_pow a b hb 0
    norm_num at hh
    exact hh
  have he1 : quinticPowerFunctional b (a) = 0 := by
    have hh := quinticPowerFunctional_pow a b hb 1
    norm_num at hh
    exact hh
  have he2 : quinticPowerFunctional b (a^2) = 0 := by
    have hh := quinticPowerFunctional_pow a b hb 2
    norm_num at hh
    exact hh
  have he3 : quinticPowerFunctional b (a^3) = 0 := by
    have hh := quinticPowerFunctional_pow a b hb 3
    norm_num at hh
    exact hh
  have he4 : quinticPowerFunctional b (a^4) = 1 := by
    have hh := quinticPowerFunctional_pow a b hb 4
    norm_num at hh
    exact hh
  have hc4 : b.repr v 4 = 0 := by
    have hp : v * (1) = b.repr v 0 • (1) + b.repr v 1 • (a) + b.repr v 2 • (a^2) + b.repr v 3 • (a^3) + b.repr v 4 • (a^4) := by
      conv_lhs => rw [hrepr]
      simp only [zero_smul, add_zero, Algebra.smul_def, map_zero, zero_mul]
      ring
    have h := hz (1)
    rw [hp] at h
    simpa only [map_add, map_smul, he0, he1, he2, he3, he4, smul_zero, smul_eq_mul, mul_one, mul_zero, zero_add, add_zero] using h
  have hc3 : b.repr v 3 = 0 := by
    have hp : v * (a) = b.repr v 0 • (a) + b.repr v 1 • (a^2) + b.repr v 2 • (a^3) + b.repr v 3 • (a^4) := by
      conv_lhs => rw [hrepr]
      rw [hc4]
      simp only [zero_smul, add_zero, Algebra.smul_def, map_zero, zero_mul]
      ring
    have h := hz (a)
    rw [hp] at h
    simpa only [map_add, map_smul, he0, he1, he2, he3, he4, smul_zero, smul_eq_mul, mul_one, mul_zero, zero_add, add_zero] using h
  have hc2 : b.repr v 2 = 0 := by
    have hp : v * (a^2) = b.repr v 0 • (a^2) + b.repr v 1 • (a^3) + b.repr v 2 • (a^4) := by
      conv_lhs => rw [hrepr]
      rw [hc3, hc4]
      simp only [zero_smul, add_zero, Algebra.smul_def, map_zero, zero_mul]
      ring
    have h := hz (a^2)
    rw [hp] at h
    simpa only [map_add, map_smul, he0, he1, he2, he3, he4, smul_zero, smul_eq_mul, mul_one, mul_zero, zero_add, add_zero] using h
  have hc1 : b.repr v 1 = 0 := by
    have hp : v * (a^3) = b.repr v 0 • (a^3) + b.repr v 1 • (a^4) := by
      conv_lhs => rw [hrepr]
      rw [hc2, hc3, hc4]
      simp only [zero_smul, add_zero, Algebra.smul_def, map_zero, zero_mul]
      ring
    have h := hz (a^3)
    rw [hp] at h
    simpa only [map_add, map_smul, he0, he1, he2, he3, he4, smul_zero, smul_eq_mul, mul_one, mul_zero, zero_add, add_zero] using h
  have hc0 : b.repr v 0 = 0 := by
    have hp : v * (a^4) = b.repr v 0 • (a^4) := by
      conv_lhs => rw [hrepr]
      rw [hc1, hc2, hc3, hc4]
      simp only [zero_smul, add_zero, Algebra.smul_def, map_zero, zero_mul]
      ring
    have h := hz (a^4)
    rw [hp] at h
    simpa only [map_add, map_smul, he0, he1, he2, he3, he4, smul_zero, smul_eq_mul, mul_one, mul_zero, zero_add, add_zero] using h
  conv_lhs => rw [hrepr]
  rw [hc0, hc1, hc2, hc3, hc4]
  simp only [zero_smul, add_zero]

end
end PfaffianDescent

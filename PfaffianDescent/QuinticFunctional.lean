import PfaffianDescent.QuinticGenerator

namespace PfaffianDescent
open Module

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A functional killing the first four power-basis vectors detects the last one. -/
theorem quintic_functional_last_ne_zero (α : L) (b : Basis (Fin 5) K L)
    (hb : ∀ i, b i = α^(i : ℕ)) (ell : Module.Dual K L) (hell : ell ≠ 0)
    (hpow : ∀ i : Fin 4, ell (α^(i : ℕ)) = 0) : ell (α^4) ≠ 0 := by
  intro hz
  have hall : ∀ i : Fin 5, ell (b i) = 0 := by
    intro i
    rw [hb]
    fin_cases i
    · exact hpow 0
    · exact hpow 1
    · exact hpow 2
    · exact hpow 3
    · exact hz
  apply hell
  ext z
  calc
    ell z = ell (∑ i, b.repr z i • b i) := congrArg ell (b.sum_repr z).symm
    _ = 0 := by simp only [map_sum, map_smul, hall, smul_zero, Finset.sum_const_zero]

/-- If a functional kills four successive powers and also β, αβ, α²β,
then β is a linear combination of 1 and α. -/
theorem quintic_functional_forces_pair (α : L) (b : Basis (Fin 5) K L)
    (hb : ∀ i, b i = α^(i : ℕ)) (ell : Module.Dual K L) (hell : ell ≠ 0)
    (hpow : ∀ i : Fin 4, ell (α^(i : ℕ)) = 0) (β : L)
    (hβ : ell β = 0) (hαβ : ell (α * β) = 0) (hααβ : ell (α^2 * β) = 0) :
    ∃ a d : K, β = algebraMap K L a + algebraMap K L d * α := by
  have hlast := quintic_functional_last_ne_zero α b hb ell hell hpow
  have h0 : ell (α^0) = 0 := hpow 0
  have h1 : ell (α^1) = 0 := hpow 1
  have h2 : ell (α^2) = 0 := hpow 2
  have h3 : ell (α^3) = 0 := hpow 3
  let d := b.repr β
  have hexp := (b.sum_repr β).symm
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, hb] at hexp
  change β = d 0 • α^0 + (d 1 • α^1 + (d 2 • α^2 + (d 3 • α^3 + d 4 • α^4))) at hexp
  have hd4 : d 4 = 0 := by
    have h := congrArg ell hexp
    simp only [map_add, map_smul, smul_eq_mul, hβ, h0, h1, h2, h3, mul_zero, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hlast
  have hd3 : d 3 = 0 := by
    have h := congrArg (fun z => ell (α * z)) hexp
    simp only [mul_add, mul_smul_comm, ← pow_succ', map_add, map_smul, smul_eq_mul,
      hαβ, h1, h2, h3, hd4, zero_mul, mul_zero, add_zero, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hlast
  have hd2 : d 2 = 0 := by
    have h := congrArg (fun z => ell (α^2 * z)) hexp
    simp only [mul_add, mul_smul_comm, ← pow_add, map_add, map_smul, smul_eq_mul,
      hααβ, h2, h3, hd3, hd4, zero_mul, mul_zero, add_zero, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hlast
  refine ⟨d 0, d 1, ?_⟩
  simpa only [hd2, hd3, hd4, zero_smul, add_zero, pow_zero, pow_one, Algebra.smul_def,
    mul_one, map_zero, zero_mul] using hexp

end
end PfaffianDescent

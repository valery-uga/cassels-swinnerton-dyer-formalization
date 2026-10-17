import PfaffianDescent.QuinticDescent

namespace PfaffianDescent
open Module
open scoped BigOperators

/-- A degree-five sum contains a positive term whose underlying point degree is
at most two or exactly five. -/
theorem degree_five_small_summand {ι : Type*} [Fintype ι] (w d : ι → ℕ)
    (hdegree : ∑ i, w i * d i = 5) :
    ∃ i, w i ≠ 0 ∧ (d i ≤ 2 ∨ d i = 5) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, w i * d i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∑ i, w i * d i = 0 := Finset.sum_eq_zero (fun i _ => h i)
    omega
  have hwi : w i ≠ 0 := (mul_ne_zero_iff.mp hi).1
  by_cases hsmall : d i ≤ 2
  · exact ⟨i, hwi, Or.inl hsmall⟩
  by_cases hfive : d i = 5
  · exact ⟨i, hwi, Or.inr hfive⟩
  have hlow : d i ≤ w i * d i := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hwi)
  have hhigh : w i * d i ≤ 5 := by
    rw [← hdegree]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (w j * d j)) (Finset.mem_univ i)
  have hterm : w i * d i ≠ 5 := by
    intro h
    have hdvd : d i ∣ 5 := ⟨w i, by simpa only [mul_comm] using h.symm⟩
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdvd with he | he
    · omega
    · exact hfive he
  have hsum := Finset.sum_erase_add Finset.univ (fun j => w j * d j) (Finset.mem_univ i)
  rw [hdegree] at hsum
  obtain ⟨j, hj, hne⟩ : ∃ j ∈ Finset.univ.erase i, w j * d j ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∑ j ∈ Finset.univ.erase i, w j * d j = 0 :=
      Finset.sum_eq_zero (fun j hj => h j hj)
    omega
  have hwj : w j ≠ 0 := (mul_ne_zero_iff.mp hne).1
  have hlowj : d j ≤ w j * d j := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hwj)
  have hhighj : w j * d j ≤ ∑ j ∈ Finset.univ.erase i, w j * d j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (w j * d j)) hj
  exact ⟨j, hwj, Or.inl (by omega)⟩

section
variable {K : Type*} [Field K] [CharZero K]

/-- The effective degree-five theorem in homogeneous coordinates. Each summand
is given over a finite residue field; arbitrary nonnegative multiplicities are allowed. -/
theorem effective_degree_five_to_point {ι : Type*} [Fintype ι]
    (L : ι → Type*) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    (c : Cubic K 4) (w : ι → ℕ) (p : ∀ i, Vec (L i) 4)
    (hp : ∀ i, w i ≠ 0 → p i ≠ 0)
    (hF : ∀ i, w i ≠ 0 → (c.map (algebraMap K (L i))).eval (p i) = 0)
    (hdegree : ∑ i, w i * finrank K (L i) = 5) :
    ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  obtain ⟨i, hi, hd⟩ := degree_five_small_summand w (fun i => finrank K (L i)) hdegree
  rcases hd with hd | hd
  · exact cubic_degree_le_two_secant hd c (p i) (hp i hi) (hF i hi)
  · exact cubic_degree_five_descent hd c (p i) (hp i hi) (hF i hi)

end
end PfaffianDescent

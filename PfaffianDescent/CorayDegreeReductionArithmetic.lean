import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Actual degree-selection arithmetic in Coray Theorem 6.1 and 7.1

These are complete arithmetic proofs only. They do not construct a divisor,
prove Riemann–Roch, identify genus, or certify a geometric reduction.
The triangular number `3 * l.choose 2` is `3*l*(l-1)/2`.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

namespace PfaffianDescent.Coray

private theorem exists_positive_three_nondivisible_in_pair (a : ℕ) (ha : 0 < a) :
    ∃ b : ℕ, a ≤ b ∧ b ≤ a + 1 ∧ 0 < b ∧ ¬ 3 ∣ b := by
  by_cases h : 3 ∣ a
  · refine ⟨a + 1, by omega, le_rfl, by omega, ?_⟩
    rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
    omega
  · exact ⟨a, le_rfl, by omega, ha, h⟩

/-- Actual positive multiple selection; valid also for genus zero. -/
theorem exists_positive_multiple_prime_to_three_in_genus_window
    (delta g : ℕ) (hdelta : 0 < delta) (hprime : ¬ 3 ∣ delta) :
    ∃ theta : ℕ, 0 < theta ∧ delta ∣ theta ∧ ¬ 3 ∣ theta ∧
      g ≤ theta ∧ theta < g + 2 * delta := by
  by_cases hg : g = 0
  · subst g
    exact ⟨delta, hdelta, dvd_rfl, hprime, Nat.zero_le _, by omega⟩
  let t := (g - 1) / delta
  let r := (g - 1) % delta
  have hr : r < delta := Nat.mod_lt _ hdelta
  have hdiv : g - 1 = t * delta + r := by
    simpa only [t, r, Nat.mul_comm, Nat.add_comm] using
      (Nat.mod_add_div (g - 1) delta).symm
  obtain ⟨b, hbmin, hbmax, hbpos, hbprime⟩ :=
    exists_positive_three_nondivisible_in_pair (t + 1) (Nat.succ_pos t)
  have hlower : g ≤ (t + 1) * delta := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hupper : (t + 2) * delta < g + 2 * delta := by
    rw [Nat.add_mul]
    omega
  refine ⟨b * delta, Nat.mul_pos hbpos hdelta, ⟨b, Nat.mul_comm _ _⟩,
    (show Nat.Prime 3 by decide).not_dvd_mul hbprime hprime, ?_, ?_⟩
  · exact hlower.trans (Nat.mul_le_mul_right delta hbmin)
  · exact (Nat.mul_le_mul_right delta hbmax).trans_lt hupper

/-- The actual gcd-type divisor of `3*l` prime to three divides `l`. -/
theorem degree_delta_dvd_l_of_dvd_three_l
    (delta l : ℕ) (hprime : ¬ 3 ∣ delta) (hdiv : delta ∣ 3 * l) :
    delta ∣ l := by
  have hcop : Nat.Coprime delta 3 :=
    ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr hprime).symm
  exact hcop.dvd_of_dvd_mul_left hdiv

private theorem coray_triangular_step (l : ℕ) :
    3 * (l + 1).choose 2 = 3 * l.choose 2 + 3 * l := by
  rw [Nat.choose_succ_succ' l 1, Nat.choose_one_right]
  ring

/-- Exact arithmetic of A(ii): no extra interpolation constraints are needed
when the freedom is below three. All premises are ordinary integers. -/
theorem coray_case_Aii_degree_selection
    (l d g delta : ℕ) (hl : 3 ≤ l)
    (hdelta : 0 < delta) (hprime : ¬ 3 ∣ delta) (hdiv : delta ∣ 3 * l)
    (hgenus : g ≤ 3 * l.choose 2 + 1)
    (hdegree : d ≤ 3 * (l + 1).choose 2)
    (hfreedom : 3 * (l + 1).choose 2 - d < 3) :
    ∃ theta : ℕ, 0 < theta ∧ delta ∣ theta ∧ ¬ 3 ∣ theta ∧ g ≤ theta ∧ theta < d := by
  have hdeltal := degree_delta_dvd_l_of_dvd_three_l delta l hprime hdiv
  have hsmall : delta ≤ l := Nat.le_of_dvd (by omega : 0 < l) hdeltal
  obtain ⟨theta, hpos, hmultiple, hprimeTheta, hlow, hhigh⟩ :=
    exists_positive_multiple_prime_to_three_in_genus_window delta g hdelta hprime
  have hstep := coray_triangular_step l
  refine ⟨theta, hpos, hmultiple, hprimeTheta, hlow, ?_⟩
  omega

private theorem twice_choose_two (l : ℕ) : 2 * l.choose 2 = l * (l - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose l 2
  rw [show Nat.factorial 2 = 2 by decide] at h
  simpa only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    mul_one, mul_comm] using h.symm

/-- At the boundary degree, the actual divisor delta of both l and d can
only be one or two. This derives the alternatives; it does not assume them. -/
theorem coray_boundary_delta_eq_one_or_two
    (l delta : ℕ) (hdivl : delta ∣ l) (hdivd : delta ∣ 3 * l.choose 2 + 1) :
    delta = 1 ∨ delta = 2 := by
  have htwo : 2 * (3 * l.choose 2 + 1) = 3 * l * (l - 1) + 2 := by
    have h := twice_choose_two l
    calc
      2 * (3 * l.choose 2 + 1) = 3 * (2 * l.choose 2) + 2 := by ring
      _ = 3 * l * (l - 1) + 2 := by rw [h]; ring
  have hproduct : delta ∣ 3 * l * (l - 1) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdivl 3) (l - 1)
  have hsum : delta ∣ 3 * l * (l - 1) + 2 := by
    rw [← htwo]
    exact dvd_mul_of_dvd_right hdivd 2
  have hdivtwo : delta ∣ 2 := (Nat.dvd_add_iff_right hproduct).2 hsum
  exact Nat.prime_two.eq_one_or_self_of_dvd delta hdivtwo

/-- Exact boundary A(iii) candidates after the numerical genus drop of three:
the candidate is d−3 or d−2 and is positive, a multiple of delta, prime to
three, at least g and strictly below d. No genus drop is geometrically proved
or certified by this ordinary arithmetic statement. -/
theorem coray_case_Aiii_degree_selection
    (l g delta : ℕ) (hl : 2 ≤ l) (hdivl : delta ∣ l)
    (hdivd : delta ∣ 3 * l.choose 2 + 1) (hgenus : g + 3 ≤ 3 * l.choose 2 + 1) :
    let d := 3 * l.choose 2 + 1
    ∃ theta : ℕ, (theta = d - 3 ∨ theta = d - 2) ∧
      0 < theta ∧ delta ∣ theta ∧ ¬ 3 ∣ theta ∧ g ≤ theta ∧ theta < d := by
  have hchoose : 0 < l.choose 2 := Nat.choose_pos hl
  have hd : 4 ≤ 3 * l.choose 2 + 1 := by omega
  rcases coray_boundary_delta_eq_one_or_two l delta hdivl hdivd with h | h
  · subst delta
    refine ⟨3 * l.choose 2 + 1 - 3, Or.inl rfl, by omega, one_dvd _, ?_, by omega, by omega⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  · subst delta
    refine ⟨3 * l.choose 2 + 1 - 2, Or.inr rfl, by omega, ?_, ?_, by omega, by omega⟩
    · rw [Nat.dvd_iff_mod_eq_zero] at hdivd ⊢
      omega
    · rw [Nat.dvd_iff_mod_eq_zero]
      omega

/-- Nine AUXILIARY degree-three full-jet conditions fit exactly when l≥4.
Ordinary interpolation at the original boundary point has already cost d. -/
theorem coray_boundary_nine_conditions_iff
    (l : ℕ) (hl : 1 ≤ l) :
    9 ≤ 3 * (l + 1).choose 2 - (3 * l.choose 2 + 1) ↔ 4 ≤ l := by
  have hstep := coray_triangular_step l
  omega

/-- The two insufficient-room boundary degrees beyond degree one are exactly
four and ten. This is arithmetic only, not a proof of Coray reduction. -/
theorem coray_boundary_insufficient_room_degrees
    (l : ℕ) (hl : 2 ≤ l)
    (hroom : ¬ 9 ≤ 3 * (l + 1).choose 2 - (3 * l.choose 2 + 1)) :
    (l = 2 ∧ 3 * l.choose 2 + 1 = 4) ∨
      (l = 3 ∧ 3 * l.choose 2 + 1 = 10) := by
  have hsmall : l < 4 := by
    rw [coray_boundary_nine_conditions_iff l (by omega)] at hroom
    omega
  have hcases : l = 2 ∨ l = 3 := by omega
  rcases hcases with rfl | rfl
  · exact Or.inl ⟨rfl, by decide⟩
  · exact Or.inr ⟨rfl, by decide⟩

end PfaffianDescent.Coray

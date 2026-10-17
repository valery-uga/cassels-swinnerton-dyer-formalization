import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic
import PfaffianDescent.CorayDegreeReductionArithmetic

/-! Exact smaller original-degree comparisons for the sharp OWN word interval.
No geometric incidence, proper-component selection or point result is assumed. -/
namespace PfaffianDescent.Coray
set_option autoImplicit false

private theorem scaledSharpWordUpper_lt_productGenus
    (r lambda : ℕ) (hr : 2 ≤ r) (hlambda : 1 ≤ lambda)
    (hLarge : 3 ≤ r ∨ 2 ≤ lambda) :
    r * (3 * lambda.choose 2 + 2 * lambda) <
      1 + 3 * (r * lambda).choose 2 := by
  have hrQ : (2 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr
  have hlambdaQ : (1 : ℚ) ≤ (lambda : ℚ) := by exact_mod_cast hlambda
  have hProduct : (2 : ℚ) ≤ ((r : ℚ) - 1) * (lambda : ℚ) := by
    rcases hLarge with hR | hLambda
    · have hRQ : (3 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hR
      have h := mul_le_mul_of_nonneg_left hlambdaQ
        (show (0 : ℚ) ≤ (r : ℚ) - 1 by linarith)
      nlinarith
    · have hLambdaQ : (2 : ℚ) ≤ (lambda : ℚ) := by exact_mod_cast hLambda
      have h := mul_le_mul_of_nonneg_right
        (show (1 : ℚ) ≤ (r : ℚ) - 1 by linarith)
        (show (0 : ℚ) ≤ (lambda : ℚ) by linarith)
      nlinarith
  have hFactor : (0 : ℚ) < 3 * ((r : ℚ) - 1) * (lambda : ℚ) - 4 := by
    nlinarith
  have hPositive : (0 : ℚ) <
      2 + (r : ℚ) * (lambda : ℚ) *
        (3 * ((r : ℚ) - 1) * (lambda : ℚ) - 4) := by
    have h := mul_pos
      (mul_pos (show (0 : ℚ) < (r : ℚ) by linarith)
        (show (0 : ℚ) < (lambda : ℚ) by linarith)) hFactor
    linarith
  have hIdentity : (2 : ℚ) * (1 + 3 * ((r * lambda).choose 2 : ℚ)) -
      2 * (r : ℚ) * (3 * (lambda.choose 2 : ℚ) + 2 * (lambda : ℚ)) =
      2 + (r : ℚ) * (lambda : ℚ) *
        (3 * ((r : ℚ) - 1) * (lambda : ℚ) - 4) := by
    rw [Nat.cast_choose_two ℚ (r * lambda), Nat.cast_choose_two ℚ lambda]
    push_cast
    ring
  have hStrictQ : (r : ℚ) * (3 * (lambda.choose 2 : ℚ) + 2 * (lambda : ℚ)) <
      1 + 3 * ((r * lambda).choose 2 : ℚ) := by linarith
  exact_mod_cast hStrictQ

/-- The scaled OWN word interval is strictly below every original degree
in the lower Coray window except degree four. In the only small product
r=2,lambda=1 the comparison is proved directly, preserving the n=2 edge. -/
theorem coray_scaledSharpWordUpper_lt_originalDegree_outside_four001
    (r lambda n d : ℕ) (hr : 2 ≤ r) (hlambda : 1 ≤ lambda)
    (hDegree : r * lambda ≤ n) (hWindow : 1 + 3 * n.choose 2 ≤ d)
    (hNotFour : d ≠ 4) :
    r * (3 * lambda.choose 2 + 2 * lambda) < d := by
  by_cases hLarge : 3 ≤ r ∨ 2 ≤ lambda
  · have hStrict := scaledSharpWordUpper_lt_productGenus r lambda hr hlambda hLarge
    have hChoose : (r * lambda).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hDegree
    exact hStrict.trans_le
      ((Nat.add_le_add_left (Nat.mul_le_mul_left 3 hChoose) 1).trans hWindow)
  · have hR : r = 2 := by omega
    have hLambda : lambda = 1 := by omega
    subst r
    subst lambda
    by_cases hn : n = 2
    · subst n
      norm_num at hWindow ⊢
      omega
    · have hn3 : 3 ≤ n := by omega
      have hChoose : (3 : ℕ).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hn3
      norm_num at hChoose ⊢
      omega

/-- For field degree one, an actual strict component degree lambda<n
already puts the full sharp word interval below the original lower window.
No strict-component conclusion is supplied or inferred here. -/
theorem coray_properOwnSharpWordUpper_lt_originalDegree001
    (lambda n d : ℕ) (hlambda : 1 ≤ lambda) (hProper : lambda < n)
    (hWindow : 1 + 3 * n.choose 2 ≤ d) :
    3 * lambda.choose 2 + 2 * lambda < d := by
  have hStep : 3 * (lambda + 1).choose 2 = 3 * lambda.choose 2 + 3 * lambda := by
    simpa only [Nat.reduceAdd, Nat.choose_one_right, Nat.mul_add, Nat.add_comm] using
      congrArg (fun t : ℕ => 3 * t) (Nat.choose_succ_succ' lambda 1)
  have hChoose : (lambda + 1).choose 2 ≤ n.choose 2 :=
    Nat.choose_le_choose 2 (by omega)
  omega

/-- Construct the literal positive prime-to-three gcd multiple in the sharp
OWN interval and prove its SCALED original degree is smaller. All hypotheses
are numerical inputs of the actual cycle selector, with degree four explicit. -/
theorem coray_scaledSharpWordWindow_exists_multiple_smaller_originalDegree001
    (r lambda n d delta : ℕ) (hr : 2 ≤ r) (hlambda : 1 ≤ lambda)
    (hDegree : r * lambda ≤ n) (hWindow : 1 + 3 * n.choose 2 ≤ d)
    (hNotFour : d ≠ 4) (hDelta : 0 < delta)
    (hDeltaPrime : ¬ 3 ∣ delta) (hDeltaDegree : delta ∣ 3 * lambda) :
    ∃ theta : ℕ, 0 < theta ∧ delta ∣ theta ∧ ¬ 3 ∣ theta ∧
      1 + 3 * lambda.choose 2 ≤ theta ∧ r * theta < d := by
  have hDiv := degree_delta_dvd_l_of_dvd_three_l delta lambda hDeltaPrime hDeltaDegree
  have hSmall : delta ≤ lambda := Nat.le_of_dvd (by omega) hDiv
  obtain ⟨theta, hPos, hMultiple, hPrime, hLow, hHigh⟩ :=
    exists_positive_multiple_prime_to_three_in_genus_window delta
      (1 + 3 * lambda.choose 2) hDelta hDeltaPrime
  have hTheta : theta ≤ 3 * lambda.choose 2 + 2 * lambda := by omega
  have hUpper := coray_scaledSharpWordUpper_lt_originalDegree_outside_four001
    r lambda n d hr hlambda hDegree hWindow hNotFour
  exact ⟨theta, hPos, hMultiple, hPrime, hLow,
    (Nat.mul_le_mul_left r hTheta).trans_lt hUpper⟩

/-- The corresponding field-degree-one/proper-component interval produces
its prime-to-three gcd multiple with a strict original degree comparison. -/
theorem coray_properOwnSharpWordWindow_exists_multiple_smaller_originalDegree001
    (lambda n d delta : ℕ) (hlambda : 1 ≤ lambda) (hProper : lambda < n)
    (hWindow : 1 + 3 * n.choose 2 ≤ d) (hDelta : 0 < delta)
    (hDeltaPrime : ¬ 3 ∣ delta) (hDeltaDegree : delta ∣ 3 * lambda) :
    ∃ theta : ℕ, 0 < theta ∧ delta ∣ theta ∧ ¬ 3 ∣ theta ∧
      1 + 3 * lambda.choose 2 ≤ theta ∧ theta < d := by
  have hDiv := degree_delta_dvd_l_of_dvd_three_l delta lambda hDeltaPrime hDeltaDegree
  have hSmall : delta ≤ lambda := Nat.le_of_dvd (by omega) hDiv
  obtain ⟨theta, hPos, hMultiple, hPrime, hLow, hHigh⟩ :=
    exists_positive_multiple_prime_to_three_in_genus_window delta
      (1 + 3 * lambda.choose 2) hDelta hDeltaPrime
  have hTheta : theta ≤ 3 * lambda.choose 2 + 2 * lambda := by omega
  have hUpper := coray_properOwnSharpWordUpper_lt_originalDegree001
    lambda n d hlambda hProper hWindow
  exact ⟨theta, hPos, hMultiple, hPrime, hLow, hTheta.trans_lt hUpper⟩

end PfaffianDescent.Coray

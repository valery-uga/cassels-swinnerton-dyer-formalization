import Mathlib.Data.Nat.GCD.Basic
import Lean.Elab.Tactic.Omega

/-! Exact arithmetic cut for the SAME r*nu=d*s incidence identity. -/
namespace PfaffianDescent.Coray
set_option autoImplicit false

/-- A positive actual own component degree and its cubic-intersection
product bound bound the SAME model field degree. -/
theorem modelFieldDegree_le_cubicDegree_of_positiveOwnDegree001
    (r mu n : ℕ) (hmu : 0 < mu) (hProduct : r * mu ≤ 3 * n) :
    r ≤ 3 * n := by
  have hOne : 1 ≤ mu := by omega
  have h := Nat.le_trans (Nat.mul_le_mul_left r hOne) hProduct
  simpa only [Nat.mul_one] using h

/-- The actual local/global inequality, original point degree window and
native incidence rank identity give s<=2 and BOTH r and nu coprime to 3.
No desired small rank/coprimality or transitivity certificate is supplied. -/
theorem entireIncidenceRank_small_and_modelDegrees_coprime_three001
    (r nu d s genus n : ℕ)
    (hS : 0 < s) (hRank : r * nu = d * s)
    (hLocalGlobal : d * (s - 1) ≤ r + genus)
    (hR : r ≤ 3 * n) (hWindow : 3 * n < d) (hGenus : genus ≤ d)
    (hD : Nat.Coprime d 3) :
    s ≤ 2 ∧ Nat.Coprime s 3 ∧ Nat.Coprime r 3 ∧
      Nat.Coprime nu 3 ∧ Nat.Coprime (r * nu) 3 := by
  have hSmall : s ≤ 2 := by
    by_contra h
    have hTwo : 2 ≤ s - 1 := by omega
    have hLower : 2 * d ≤ d * (s - 1) := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left d hTwo
    omega
  have hSCoprime : Nat.Coprime s 3 := by
    have hCases : s = 1 ∨ s = 2 := by omega
    rcases hCases with h | h
    · subst s
      decide
    · subst s
      decide
  have hProduct : Nat.Coprime (r * nu) 3 := by
    rw [hRank]
    exact Nat.coprime_mul_iff_left.mpr ⟨hD, hSCoprime⟩
  obtain ⟨hRCoprime, hNuCoprime⟩ := Nat.coprime_mul_iff_left.mp hProduct
  exact ⟨hSmall, hSCoprime, hRCoprime, hNuCoprime, hProduct⟩

end PfaffianDescent.Coray

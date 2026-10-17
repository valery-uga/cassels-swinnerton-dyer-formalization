import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.JacobsonSpace
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Degrees of zero-cycles

Zero-cycles here are finitely supported integer combinations of the actual
closed points of a Mathlib scheme. Their degree is computed from Mathlib's
residue-field extension degree. The elementary arguments in Sections 1 and 6
of the addendum therefore do not assume effectivity or separability implicitly.
-/

open scoped BigOperators
open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

/-- If a signed sum of point degrees is not divisible by a prime, one of the
point degrees occurring in its support is not divisible by that prime. -/
theorem exists_degree_not_dvd_of_signed_sum {ι : Type*}
    (s : Finset ι) (weight : ι → ℤ) (degree : ι → ℕ) (p : ℕ)
    (h : ¬ (p : ℤ) ∣ ∑ i ∈ s, weight i * degree i) :
    ∃ i ∈ s, ¬ p ∣ degree i := by
  by_contra hn
  push Not at hn
  apply h
  apply Finset.dvd_sum
  intro i hi
  exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr (hn i hi)) _

/-- An effective cycle of total degree four has a support point of degree one,
two, or four. No assumption that the individual residue extensions are separable
is used. -/
theorem exists_degree_one_two_four_of_sum_four {ι : Type*}
    (s : Finset ι) (weight degree : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < weight i)
    (h : ∑ i ∈ s, weight i * degree i = 4) :
    ∃ i ∈ s, degree i = 1 ∨ degree i = 2 ∨ degree i = 4 := by
  have hn : ∃ i ∈ s, ¬ 3 ∣ degree i := by
    by_contra hn
    push Not at hn
    have hd : 3 ∣ ∑ i ∈ s, weight i * degree i :=
      Finset.dvd_sum (fun i hi => dvd_mul_of_dvd_right (hn i hi) _)
    omega
  obtain ⟨i, hi, hd⟩ := hn
  have hbound : degree i ≤ 4 := by
    calc
      degree i ≤ weight i * degree i := Nat.le_mul_of_pos_left _ (hw i hi)
      _ ≤ ∑ j ∈ s, weight j * degree j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (weight j * degree j)) hi
      _ = 4 := h
  refine ⟨i, hi, ?_⟩
  omega

universe u

/-- Integral zero-cycles on a scheme, before rational equivalence. -/
abbrev ZeroCycle (X : Scheme.{u}) := closedPoints X →₀ ℤ

/-- Effective zero-cycles on a scheme, before rational equivalence. -/
abbrev EffectiveZeroCycle (X : Scheme.{u}) := closedPoints X →₀ ℕ

namespace ZeroCycle
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The degree homomorphism uses the actual field degrees at the closed points.
For schemes of finite type over a field, these are finite extension degrees. -/
noncomputable def degree : ZeroCycle X →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun x : closedPoints X => (f.residueDegree x : ℤ))

theorem degree_eq_sum (z : ZeroCycle X) :
    degree f z = ∑ x ∈ z.support, z x * (f.residueDegree x : ℤ) := rfl

@[simp] theorem degree_single (x : closedPoints X) (n : ℤ) :
    degree f (Finsupp.single x n) = n * (f.residueDegree x : ℤ) := by
  simp [degree]

/-- A degree-one zero-cycle has a support point of degree coprime to three,
even when some coefficients of the cycle are negative. -/
theorem exists_coprime_degree (z : ZeroCycle X) (hz : degree f z = 1) :
    ∃ x ∈ z.support, Nat.Coprime (f.residueDegree x) 3 := by
  have hn : ¬ (3 : ℤ) ∣ ∑ x ∈ z.support, z x * (f.residueDegree x : ℤ) := by
    rw [← degree_eq_sum, hz]
    norm_num
  obtain ⟨x, hx, hd⟩ := exists_degree_not_dvd_of_signed_sum
    z.support z (fun x => f.residueDegree x) 3 hn
  exact ⟨x, hx, (Nat.prime_three.coprime_iff_not_dvd.mpr hd).symm⟩

/-- A degree-three cycle and a point of degree coprime to three explicitly give
a degree-one zero-cycle by Bézout's identity. Producing the degree-three cycle
geometrically is a separate assertion. -/
theorem exists_degree_one_of_coprime (z₃ : ZeroCycle X) (hz₃ : degree f z₃ = 3)
    (x : closedPoints X) (hx : Nat.Coprime (f.residueDegree x) 3) :
    ∃ z : ZeroCycle X, degree f z = 1 := by
  let d := f.residueDegree x
  refine ⟨Nat.gcdA d 3 • Finsupp.single x 1 + Nat.gcdB d 3 • z₃, ?_⟩
  have hb := Nat.gcd_eq_gcd_ab d 3
  have hd : Nat.gcd d 3 = 1 := hx
  rw [hd] at hb
  simp only [map_add, map_smul, degree_single, one_mul, hz₃, smul_eq_mul]
  change Nat.gcdA d 3 * (d : ℤ) + Nat.gcdB d 3 * 3 = 1
  simpa only [Nat.cast_one, Nat.cast_ofNat, mul_comm] using hb.symm

end ZeroCycle

namespace EffectiveZeroCycle
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The natural-number degree of an effective zero-cycle. -/
noncomputable def degree (z : EffectiveZeroCycle X) : ℕ :=
  z.sum (fun x n => n * f.residueDegree x)

/-- The support alternative used after specializing a length-four subscheme. -/
theorem exists_degree_one_two_four (z : EffectiveZeroCycle X) (hz : degree f z = 4) :
    ∃ x ∈ z.support,
      f.residueDegree x = 1 ∨ f.residueDegree x = 2 ∨ f.residueDegree x = 4 := by
  exact exists_degree_one_two_four_of_sum_four z.support z (fun x => f.residueDegree x)
    (fun x hx => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)) hz

end EffectiveZeroCycle
end AllCharacteristics

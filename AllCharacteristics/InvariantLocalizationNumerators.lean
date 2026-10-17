import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Invariant numerators after localization

For a finite group acting compatibly on a ring and its localization at a fixed
element, every invariant localized element admits an invariant numerator.
A single power clears the finitely many equations expressing invariance.
This works with zero divisors and in every characteristic, without averaging.
-/

open scoped BigOperators
namespace AllCharacteristics
universe u v w
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (G : Type w) [Group G] [Finite G]
variable [MulSemiringAction G A] [MulSemiringAction G B] [SMulDistribClass G A B]
variable (t : A) [IsLocalization.Away t B] (ht : ∀ g : G, g • t = t)

include ht

/-- If an element becomes invariant after localization at a fixed denominator,
a single denominator power makes its numerator invariant in the original ring. -/
theorem exists_invariant_multiple_of_invariant_image (a : A)
    (ha : ∀ g : G, g • algebraMap A B a = algebraMap A B a) :
    ∃ N : ℕ, ∀ g : G, g • (t ^ N * a) = t ^ N * a := by
  classical
  let := Fintype.ofFinite G
  have he : ∀ g : G, ∃ n : ℕ, t ^ n * (g • a) = t ^ n * a := by
    intro g
    apply IsLocalization.Away.exists_of_eq t (S := B)
    exact (algebraMap.coe_smul' g a B).trans (ha g)
  choose n hn using he
  let N := ∑ g : G, n g
  have hle (g : G) : n g ≤ N :=
    Finset.single_le_sum (fun i _ ↦ Nat.zero_le (n i)) (Finset.mem_univ g)
  have hN (g : G) : t ^ N * (g • a) = t ^ N * a := by
    have h := congrArg (fun z ↦ t ^ (N - n g) * z) (hn g)
    calc
      t ^ N * (g • a) = t ^ (N - n g) * (t ^ n g * (g • a)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hle g)]
      _ = t ^ (N - n g) * (t ^ n g * a) := h
      _ = t ^ N * a := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hle g)]
  refine ⟨N, fun g ↦ ?_⟩
  rw [smul_mul', smul_pow', ht g]
  exact hN g

/-- Every invariant localized element has an invariant numerator and a power
of the same fixed denominator, even when the original ring has zero divisors. -/
theorem exists_invariant_localization_numerator (b : B) (hb : ∀ g : G, g • b = b) :
    ∃ (N : ℕ) (a : A), (∀ g : G, g • a = a) ∧
      b * algebraMap A B t ^ N = algebraMap A B a := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj t b
  have hf : ∀ g : G, g • algebraMap A B a = algebraMap A B a := by
    intro g
    calc
      g • algebraMap A B a = g • (b * algebraMap A B t ^ n) := congrArg (g • ·) ha.symm
      _ = b * algebraMap A B t ^ n := by
        rw [smul_mul', smul_pow', hb g, ← algebraMap.coe_smul' g t B, ht g]
      _ = algebraMap A B a := ha
  obtain ⟨m, hm⟩ := exists_invariant_multiple_of_invariant_image G t ht a hf
  refine ⟨n + m, t ^ m * a, hm, ?_⟩
  calc
    b * algebraMap A B t ^ (n + m) = (b * algebraMap A B t ^ n) * algebraMap A B t ^ m := by
      rw [pow_add, mul_assoc]
    _ = algebraMap A B a * algebraMap A B t ^ m := congrArg (fun z ↦ z * algebraMap A B t ^ m) ha
    _ = algebraMap A B (t ^ m * a) := by rw [map_mul, map_pow, mul_comm]

end AllCharacteristics

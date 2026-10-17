import Mathlib.RingTheory.Localization.Defs
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Regular elements remain regular under localization

The forward implication needs no regularity assumption on the elements
being inverted. This is important for projective charts after arbitrary
base-ideal reduction, where a chart coordinate can be a zero-divisor.
-/

namespace PfaffianDescent

universe u

/-- A regular element remains regular in an arbitrary localization. -/
theorem isRegular_localization_mk_of_isRegular
    {A : Type u} [CommRing A] (M : Submonoid A)
    (q : A) (hq : IsRegular q) (m : M) :
    IsRegular (IsLocalization.mk' (Localization M) q m) := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  rw [mem_nonZeroDivisors_iff_left]
  intro y hy
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  rw [← IsLocalization.mk'_mul] at hy
  obtain ⟨t, ht⟩ :=
    (IsLocalization.mk'_eq_zero_iff (S := Localization M) (q * x) (m * s)).mp hy
  have hqx : q * ((t : A) * x) = 0 := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using ht
  have htx : (t : A) * x = 0 := by
    apply hq.left
    simpa only [mul_zero] using hqx
  exact (IsLocalization.mk'_eq_zero_iff (S := Localization M) x s).mpr ⟨t, htx⟩

end PfaffianDescent

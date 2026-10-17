import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Localization.Defs

/-!
# Cancellation in a projective homogeneous quotient

A homogeneous ideal defines a projective subscheme only after localizing on
standard affine charts.  These elementary lemmas isolate the algebraic
cancellation needed to turn a chartwise vanishing statement back into ideal
membership once multiplication by the chart denominator is injective modulo
the ideal.
-/

namespace PfaffianDescent

section

variable {R : Type*} [CommRing R]

/-- If multiplication by `z` is injective modulo `I`, a multiple of a
polynomial belonging to `I` can be cancelled. -/
theorem mem_of_mul_mem_of_quotient_mul_injective
    (I : Ideal R) (z F : R)
    (hinj : Function.Injective (fun x : R ⧸ I =>
      (Ideal.Quotient.mk I z) * x))
    (h : z * F ∈ I) : F ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hinj
  dsimp
  rw [mul_zero, ← (Ideal.Quotient.mk I).map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr h

/-- Chartwise vanishing of a polynomial implies ideal membership whenever the
chart denominator acts injectively on the quotient.  This is the local
cancellation step required for the scheme-to-ideal bridge in the
net-of-quadrics argument. -/
theorem mem_of_localization_eq_zero_of_quotient_mul_injective
    (I : Ideal R) (z F : R)
    (hinj : Function.Injective (fun x : R ⧸ I =>
      (Ideal.Quotient.mk I z) * x))
    (hzero : algebraMap (R ⧸ I)
      (Localization (Submonoid.powers (Ideal.Quotient.mk I z)))
        (Ideal.Quotient.mk I F) = 0) : F ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk I z)) _ (Ideal.Quotient.mk I F)).mp hzero
  obtain ⟨n, hn⟩ := s.2
  rw [← hn] at hs
  clear hzero s hn
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    apply ih
    apply hinj
    dsimp
    rw [mul_zero]
    simpa only [pow_succ, mul_assoc, mul_left_comm] using hs



/-- The element represented by a regular section is a non-zero-divisor in
its quotient ring. -/
theorem quotient_mk_mem_nonZeroDivisors_of_regular_mod_ideal
    (I : Ideal R) (z : R)
    (hregular : ∀ x : R, z * x ∈ I → x ∈ I) :
    Ideal.Quotient.mk I z ∈ nonZeroDivisors (R ⧸ I) := by
  rw [mem_nonZeroDivisors_iff]
  constructor <;> intro x hx
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← (Ideal.Quotient.mk I).map_mul,
      Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hregular a hx)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [mul_comm, ← (Ideal.Quotient.mk I).map_mul,
      Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hregular a hx)

/-- A section that is regular modulo a homogeneous ideal remains regular
after passing to a standard chart whose denominator is also regular modulo
that ideal. This is the ring-level input for the local Cartier equation. -/
theorem isRegular_localized_quotient_of_regular_mod_ideal
    (I : Ideal R) (z p : R)
    (hz : ∀ x : R, z * x ∈ I → x ∈ I)
    (hp : ∀ x : R, p * x ∈ I → x ∈ I) :
    IsRegular (algebraMap (R ⧸ I)
      (Localization (Submonoid.powers (Ideal.Quotient.mk I z)))
        (Ideal.Quotient.mk I p)) := by
  let M : Submonoid (R ⧸ I) := Submonoid.powers (Ideal.Quotient.mk I z)
  have hzreg : IsRegular (Ideal.Quotient.mk I z) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      (quotient_mk_mem_nonZeroDivisors_of_regular_mod_ideal I z hz)
  have hpreg : IsRegular (Ideal.Quotient.mk I p) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      (quotient_mk_mem_nonZeroDivisors_of_regular_mod_ideal I p hp)
  have hM : ∀ m ∈ M, IsRegular m := by
    intro m hm
    obtain ⟨n, rfl⟩ := hm
    exact hzreg.pow n
  simpa only [IsLocalization.mk'_one] using
    (IsLocalization.isRegular_mk' (S := Localization M) hM
      (m := 1) (r := Ideal.Quotient.mk I p)).mpr hpreg


/-- The preceding local cancellation criterion in the usual form: a
non-zero-divisor in the quotient supplies the required injectivity. -/
theorem mem_of_localization_eq_zero_of_quotient_nonZeroDivisor
    (I : Ideal R) (z F : R)
    (hreg : Ideal.Quotient.mk I z ∈ nonZeroDivisors (R ⧸ I))
    (hzero : algebraMap (R ⧸ I)
      (Localization (Submonoid.powers (Ideal.Quotient.mk I z)))
        (Ideal.Quotient.mk I F) = 0) : F ∈ I := by
  apply mem_of_localization_eq_zero_of_quotient_mul_injective I z F ?_ hzero
  intro x y hxy
  change Ideal.Quotient.mk I z * x = Ideal.Quotient.mk I z * y at hxy
  have hsub : Ideal.Quotient.mk I z * (x - y) = 0 := by
    rw [mul_sub, hxy, sub_self]
  have hzero : x - y = 0 :=
    (mul_left_mem_nonZeroDivisors_eq_zero_iff hreg).mp hsub
  exact sub_eq_zero.mp hzero

end

end PfaffianDescent

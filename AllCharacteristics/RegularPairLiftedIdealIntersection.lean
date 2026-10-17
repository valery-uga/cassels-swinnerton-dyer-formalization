import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Tactic.Ring

/-!
The actual Koszul obstruction calculation for an embedded deformation.
No square-zero, flatness, or deformation-lifting conclusion is assumed here.
-/

open scoped nonZeroDivisors
namespace AllCharacteristics
universe u v

/-- Every relation between an explicit regular pair is a Koszul relation. -/
theorem regularPair_relation_isKoszul165
    {A : Type u} [CommRing A] (f g : A)
    (hf : f ∈ A⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (A ⧸ Ideal.span {f})⁰)
    (a b : A) (h : a * f + b * g = 0) :
    ∃ c : A, a = -(c * g) ∧ b = c * f := by
  let m := Ideal.Quotient.mk (Ideal.span {f})
  have hmf : m f = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hb0 : m g * m b = 0 := by
    have hm := congrArg m h
    simpa only [map_add, map_mul, map_zero, hmf, mul_zero, zero_mul, zero_add, mul_comm] using hm
  have hbmem : b ∈ Ideal.span {f} := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((mem_nonZeroDivisors_iff_left.mp hg) (m b) hb0)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hbmem
  have ha0 : f * (a + c * g) = 0 := by
    calc
      f * (a + c * g) = a * f + b * g := by rw [hc]; ring
      _ = 0 := h
  have ha : a + c * g = 0 := (mem_nonZeroDivisors_iff_left.mp hf) _ ha0
  exact ⟨c, eq_neg_of_add_eq_zero_left ha, by simpa only [mul_comm] using hc⟩

/-- An element of the lifted ideal which reduces to zero has a presentation
whose two coefficients themselves reduce to zero.  The element and the ideal
are prescribed; only a Koszul correction is made to their coefficients. -/
theorem liftedRegularPair_kernelCoefficients165
    {A' : Type u} {A : Type v} [CommRing A'] [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (f' g' : A')
    (hf : π f' ∈ A⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {π f'}) (π g') ∈
      (A ⧸ Ideal.span {π f'})⁰)
    (x : A') (hxK : x ∈ RingHom.ker π)
    (hxJ : x ∈ Ideal.span ({f', g'} : Set A')) :
    ∃ a b : A', a ∈ RingHom.ker π ∧ b ∈ RingHom.ker π ∧
      a * f' + b * g' = x := by
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hxJ
  have hrel : π a * π f' + π b * π g' = 0 := by
    rw [← map_mul, ← map_mul, ← map_add, hab]
    exact RingHom.mem_ker.mp hxK
  obtain ⟨c, hac, hbc⟩ := regularPair_relation_isKoszul165
    (π f') (π g') hf hg (π a) (π b) hrel
  obtain ⟨c', hc'⟩ := hπ c
  refine ⟨a + c' * g', b - c' * f', ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, map_add, map_mul, hc', hac]
    exact neg_add_cancel _
  · rw [RingHom.mem_ker, map_sub, map_mul, hc', hbc]
    exact sub_self _
  · calc
      (a + c' * g') * f' + (b - c' * f') * g' = a * f' + b * g' := by ring
      _ = x := hab

/-- The actual lifted two-generator ideal has zero first reduction obstruction:
the intersection with the whole ambient reduction kernel equals its product
with that kernel.  This is not a flatness conclusion. -/
theorem liftedRegularPair_kernel_inf_eq_mul165
    {A' : Type u} {A : Type v} [CommRing A'] [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (f' g' : A')
    (hf : π f' ∈ A⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {π f'}) (π g') ∈
      (A ⧸ Ideal.span {π f'})⁰) :
    RingHom.ker π ⊓ Ideal.span ({f', g'} : Set A') =
      RingHom.ker π * Ideal.span ({f', g'} : Set A') := by
  refine le_antisymm ?_ Ideal.mul_le_inf
  intro x hx
  obtain ⟨a, b, ha, hb, hab⟩ :=
    liftedRegularPair_kernelCoefficients165 π hπ f' g' hf hg x hx.1 hx.2
  rw [← hab]
  exact Ideal.add_mem _
    (Ideal.mul_mem_mul ha (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_mul hb (Ideal.subset_span (by simp)))

/-- Both prescribed generators are retained under whole-ideal transport. -/
theorem liftedRegularPair_wholeIdeal_map165
    {A' : Type u} {A : Type v} [CommRing A'] [CommRing A]
    (π : A' →+* A) (f' g' : A') :
    (Ideal.span ({f', g'} : Set A')).map π =
      Ideal.span ({π f', π g'} : Set A) := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

end AllCharacteristics

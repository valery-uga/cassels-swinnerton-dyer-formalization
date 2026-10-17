import PfaffianDescent.TwoGeneratorKoszul
import Mathlib.Tactic.Abel
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Local coefficients of the Koszul-to-Cech transgression

Boundaries of first Koszul lifts on triple intersections have a unique
coefficient. The coefficients are Cech cocycles and respect restriction.
On the two principal opens the normalized coefficient is the actual
localization inverse of the product of the parameters.
-/

namespace PfaffianDescent
variable {R : Type*} [CommRing R]
open scoped nonZeroDivisors

/-- Differences of lifts of an augmentation are Koszul cycles on triple intersections. -/
theorem twoGeneratorLast_cech_difference_eq_zero
    (q f t₀ t₁ t₂ : R) (v₀₁ v₀₂ v₁₂ : R × R)
    (h₀₁ : twoGeneratorLast q f v₀₁ = t₁ - t₀)
    (h₀₂ : twoGeneratorLast q f v₀₂ = t₂ - t₀)
    (h₁₂ : twoGeneratorLast q f v₁₂ = t₂ - t₁) :
    twoGeneratorLast q f (v₁₂ - v₀₂ + v₀₁) = 0 := by
  rw [map_add, map_sub, h₁₂, h₀₂, h₀₁]
  abel

/-- The Koszul coefficient of a triple-intersection boundary exists uniquely
for a regular pair. -/
theorem exists_unique_koszul_cech_coefficient
    (q f : R) (hq : q ∈ R⁰)
    (hf : Ideal.Quotient.mk (Ideal.span {q}) f ∈ (R ⧸ Ideal.span {q})⁰)
    (t₀ t₁ t₂ : R) (v₀₁ v₀₂ v₁₂ : R × R)
    (h₀₁ : twoGeneratorLast q f v₀₁ = t₁ - t₀)
    (h₀₂ : twoGeneratorLast q f v₀₂ = t₂ - t₀)
    (h₁₂ : twoGeneratorLast q f v₁₂ = t₂ - t₁) :
    ∃! c : R, twoGeneratorFirst q f c = v₁₂ - v₀₂ + v₀₁ := by
  have hz := twoGeneratorLast_cech_difference_eq_zero q f t₀ t₁ t₂
    v₀₁ v₀₂ v₁₂ h₀₁ h₀₂ h₁₂
  have hrange : v₁₂ - v₀₂ + v₀₁ ∈ LinearMap.range (twoGeneratorFirst q f) := by
    rw [twoGenerator_exact_of_regular hq hf]
    exact hz
  obtain ⟨c, hc⟩ := hrange
  exact ⟨c, hc, fun y hy => twoGeneratorFirst_injective_of_regular hq (hy.trans hc.symm)⟩

/-- The same unique coefficient exists away from the common zero locus,
where the parameter ideal is the unit ideal. -/
theorem exists_unique_koszul_cech_coefficient_of_span_eq_top
    (q f : R) (hspan : Ideal.span ({q, f} : Set R) = ⊤)
    (t₀ t₁ t₂ : R) (v₀₁ v₀₂ v₁₂ : R × R)
    (h₀₁ : twoGeneratorLast q f v₀₁ = t₁ - t₀)
    (h₀₂ : twoGeneratorLast q f v₀₂ = t₂ - t₀)
    (h₁₂ : twoGeneratorLast q f v₁₂ = t₂ - t₁) :
    ∃! c : R, twoGeneratorFirst q f c = v₁₂ - v₀₂ + v₀₁ := by
  have hz := twoGeneratorLast_cech_difference_eq_zero q f t₀ t₁ t₂
    v₀₁ v₀₂ v₁₂ h₀₁ h₀₂ h₁₂
  have hrange : v₁₂ - v₀₂ + v₀₁ ∈ LinearMap.range (twoGeneratorFirst q f) := by
    rw [twoGenerator_exact_of_span_eq_top hspan]
    exact hz
  obtain ⟨c, hc⟩ := hrange
  exact ⟨c, hc, fun y hy =>
    twoGeneratorFirst_injective_of_span_eq_top hspan (hy.trans hc.symm)⟩

/-- The coefficients obtained from the Koszul lifting form a Cech two-cocycle. -/
theorem koszul_cech_coefficients_cocycle
    (q f : R) (hinj : Function.Injective (twoGeneratorFirst q f))
    (v₀₁ v₀₂ v₀₃ v₁₂ v₁₃ v₂₃ : R × R)
    (c₀₁₂ c₀₁₃ c₀₂₃ c₁₂₃ : R)
    (h₀₁₂ : twoGeneratorFirst q f c₀₁₂ = v₁₂ - v₀₂ + v₀₁)
    (h₀₁₃ : twoGeneratorFirst q f c₀₁₃ = v₁₃ - v₀₃ + v₀₁)
    (h₀₂₃ : twoGeneratorFirst q f c₀₂₃ = v₂₃ - v₀₃ + v₀₂)
    (h₁₂₃ : twoGeneratorFirst q f c₁₂₃ = v₂₃ - v₁₃ + v₁₂) :
    c₁₂₃ - c₀₂₃ + c₀₁₃ - c₀₁₂ = 0 := by
  apply hinj
  rw [map_zero, map_sub, map_add, map_sub, h₁₂₃, h₀₂₃, h₀₁₃, h₀₁₂]
  abel

/-- On the two principal opens the standard Koszul lifts give the
coefficient `1/(q f)`, with the sign fixed by the chosen Cech differential. -/
theorem koszul_cech_coefficient_of_two_inverses
    (q f uq uf : R) (hq : q * uq = 1) (hf : f * uf = 1) :
    twoGeneratorFirst q f (uq * uf) =
      (0 : R × R) - (0, -uf) + (-uq, 0) := by
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.fst_neg, neg_zero, zero_sub, zero_add]
    change -f * (uq * uf) = -uq
    linear_combination -uq * hf
  · simp only [Prod.snd_add, Prod.snd_neg, zero_sub, add_zero, neg_neg]
    change q * (uq * uf) = uf
    linear_combination uf * hq

/-- The computed normalized coefficient is forced by any Koszul lift with
the same boundary, not merely one possible coefficient. -/
theorem koszul_cech_coefficient_eq_product_inverses
    (q f uq uf c : R) (hq : q * uq = 1) (hf : f * uf = 1)
    (hc : twoGeneratorFirst q f c =
      (0 : R × R) - (0, -uf) + (-uq, 0)) : c = uq * uf := by
  have hfirst : twoGeneratorFirst q f c = twoGeneratorFirst q f (uq * uf) :=
    hc.trans (koszul_cech_coefficient_of_two_inverses q f uq uf hq hf).symm
  have heq := congrArg Prod.snd hfirst
  change q * c = q * (uq * uf) at heq
  have hleft : uq * q = 1 := by rw [mul_comm]; exact hq
  have h := congrArg (fun x : R => uq * x) heq
  simpa only [← mul_assoc, hleft, one_mul] using h

/-- On the product principal open the actual localization inverse is the
normalized Koszul-to-Cech coefficient. -/
theorem koszul_cech_coefficient_eq_localization_inverse
    (q f : R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.Away (q * f) S] (c : S)
    (hc : twoGeneratorFirst (algebraMap R S q) (algebraMap R S f) c =
      (0 : S × S) -
        (0, -(algebraMap R S q * IsLocalization.Away.invSelf (S := S) (q * f))) +
        (-(algebraMap R S f * IsLocalization.Away.invSelf (S := S) (q * f)), 0)) :
    c = IsLocalization.Away.invSelf (S := S) (q * f) := by
  let qi := algebraMap R S q
  let fi := algebraMap R S f
  let t := IsLocalization.Away.invSelf (S := S) (q * f)
  have hqi : qi * (fi * t) = 1 := by
    rw [← mul_assoc]
    exact (map_mul (algebraMap R S) q f) ▸ IsLocalization.Away.mul_invSelf (S := S) (q * f)
  have hfi : fi * (qi * t) = 1 := by
    rw [mul_left_comm]
    exact hqi
  have hc' : c = (fi * t) * (qi * t) :=
    koszul_cech_coefficient_eq_product_inverses qi fi (fi * t) (qi * t) c hqi hfi hc
  rw [hc']
  calc
    (fi * t) * (qi * t) = (qi * (fi * t)) * t := by ring
    _ = t := by rw [hqi, one_mul]

/-- Koszul coefficients commute with changing the section ring. -/
theorem twoGeneratorFirst_map {S : Type*} [CommRing S]
    (φ : R →+* S) (q f c : R) :
    twoGeneratorFirst (φ q) (φ f) (φ c) =
      (φ.prodMap φ) (twoGeneratorFirst q f c) := by
  ext <;> simp [twoGeneratorFirst]

/-- Restriction of a unique triple coefficient is the coefficient of the
restricted Koszul boundary. -/
theorem koszul_cech_coefficient_map {S : Type*} [CommRing S]
    (φ : R →+* S) (q f : R)
    (hinj : Function.Injective (twoGeneratorFirst (φ q) (φ f)))
    (v₀₁ v₀₂ v₁₂ : R × R) (c : R) (c' : S)
    (hc : twoGeneratorFirst q f c = v₁₂ - v₀₂ + v₀₁)
    (hc' : twoGeneratorFirst (φ q) (φ f) c' =
      (φ.prodMap φ) v₁₂ - (φ.prodMap φ) v₀₂ + (φ.prodMap φ) v₀₁) :
    φ c = c' := by
  apply hinj
  rw [twoGeneratorFirst_map, hc, map_add, map_sub, hc']
end PfaffianDescent

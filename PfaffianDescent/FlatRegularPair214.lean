import PfaffianDescent.LocalSerreExtensionPresentation
import Mathlib.RingTheory.Regular.Flat

/-! Source candidate: ordinary two-element regularity is preserved by an
actual flat ring homomorphism. No target regularity assumption. -/
noncomputable section
open RingTheory.Sequence
open scoped nonZeroDivisors Pointwise
namespace PfaffianDescent
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

theorem regularPair_iff_weaklyRegular214 (f g : R) :
    (f ∈ R⁰ ∧ Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰) ↔
      IsWeaklyRegular R [f, g] := by
  have heq : f • (⊤ : Submodule R R) = Ideal.span {f} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop f R ≃ₗ[R] R ⧸ Ideal.span {f} := Submodule.quotEquivOfEq _ _ heq
  have hfirst : f ∈ R⁰ ↔ IsSMulRegular R f := by
    rw [mem_nonZeroDivisors_iff_left, isSMulRegular_iff_right_eq_zero_of_smul]
    rfl
  have hsecond : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰ ↔
      IsSMulRegular (R ⧸ Ideal.span {f}) g := by
    rw [mem_nonZeroDivisors_iff_left, isSMulRegular_iff_right_eq_zero_of_smul]
    rfl
  rw [hfirst, hsecond, isWeaklyRegular_cons_iff,
    isWeaklyRegular_singleton_iff, e.isSMulRegular_congr]

theorem flatRingHom_regularPair214 (φ : R →+* S) (hφ : φ.Flat)
    (f g : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰) :
    φ f ∈ S⁰ ∧ Ideal.Quotient.mk (Ideal.span {φ f}) (φ g) ∈ (S ⧸ Ideal.span {φ f})⁰ := by
  letI : Algebra R S := φ.toAlgebra
  letI : Module.Flat R S := hφ
  have h := ((regularPair_iff_weaklyRegular214 f g).mp ⟨hf, hg⟩).of_flat (S := S)
  apply (regularPair_iff_weaklyRegular214 (φ f) (φ g)).mpr
  simpa only [List.map_cons, List.map_nil, RingHom.algebraMap_toAlgebra] using h

end PfaffianDescent

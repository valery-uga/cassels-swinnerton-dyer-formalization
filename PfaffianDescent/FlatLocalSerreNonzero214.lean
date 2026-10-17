import PfaffianDescent.FlatRegularPair214
import PfaffianDescent.FlatKoszulClassNonzero211

/-! Source candidate: flat pullback preserves an actual unit Serre class
at a proper image ideal, deriving all target regularity internally. -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

theorem actualFlatLocalSerreExtTwo_unit_ne_zero214
    [HasExt.{u + 1} (ModuleCat.{u} R)] [HasExt.{u + 1} (ModuleCat.{u} S)]
    (φ : R →+* S) (hφ : φ.Flat) (f g c : R)
    (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hc : IsUnit c) (hproper : (1 : S) ∉ Ideal.span ({φ f, φ g} : Set S)) :
    cubicPointTraceFieldBaseChangeLocalExtMap φ hφ _ _ 2
      (localSerreExtTwoClass f g c hf hg) ≠ 0 := by
  obtain ⟨hf', hg'⟩ := flatRingHom_regularPair214 φ hφ f g hf hg
  exact flatKoszulSerreExtTwo_unit_ne_zero211 φ hφ f g c hf hg hf' hg' hc hproper

end PfaffianDescent

import PfaffianDescent.LocalSerreExtensionPresentation
import PfaffianDescent.TwoStepResolutionComparison
import PfaffianDescent.ExtAcyclicResolutionMap
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # The actual two-parameter surface Yoneda class

This packages the regular two-parameter Koszul resolution with precisely
the ideal and quotient objects used by `localSerreExtTwoClass`.
-/

noncomputable section

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u w

variable {B : Type u} [CommRing B]

def pointCartierYonedaSurfaceResolution (g h : B) (hg : g ∈ B⁰)
    (hh : Ideal.Quotient.mk (Ideal.span {g}) h ∈ (B ⧸ Ideal.span {g})⁰) :
    TwoStepResolution (ModuleCat B) where
  P := ModuleCat.of B (B ⧸ Ideal.span ({g, h} : Set B))
  C₀ := ModuleCat.of B B
  C₁ := ModuleCat.of B (B × B)
  K₀ := ModuleCat.of B (Ideal.span ({g, h} : Set B))
  K₁ := ModuleCat.of B B
  i₀ := (localSerreIdealQuotientComplex g h).f
  p₀ := (localSerreIdealQuotientComplex g h).g
  zero₀ := (localSerreIdealQuotientComplex g h).zero
  i₁ := (localKoszulIdealComplex g h).f
  p₁ := (localKoszulIdealComplex g h).g
  zero₁ := (localKoszulIdealComplex g h).zero
  exact₀ := localSerreIdealQuotientComplex_shortExact g h
  exact₁ := localKoszulIdealComplex_shortExact g h hg hh

/-- The connecting class of the concrete two-step resolution is exactly
the already defined local Serre class with the same coefficient. -/
theorem pointCartierYonedaSurfaceResolution_connecting
    [hExt : HasExt.{w} (ModuleCat B)] (g h r : B) (hg : g ∈ B⁰)
    (hh : Ideal.Quotient.mk (Ideal.span {g}) h ∈ (B ⧸ Ideal.span {g})⁰) :
    (pointCartierYonedaSurfaceResolution g h hg hh).connecting (ModuleCat.of B B)
      (ModuleCat.ofHom (LinearMap.lsmul B B r)) = localSerreExtTwoClass g h r hg hh := by
  change (localSerreIdealQuotientComplex_shortExact g h).extClass.comp
    ((localKoszulIdealComplex_shortExact g h hg hh).extClass.comp
      (Ext.mk₀ (ModuleCat.ofHom (LinearMap.lsmul B B r))) (add_zero 1))
      (show 1 + 1 = 2 by rfl) = _
  rw [← localSerreExtClass_eq_koszul_boundary g h r hg hh]
  rfl

end PfaffianDescent

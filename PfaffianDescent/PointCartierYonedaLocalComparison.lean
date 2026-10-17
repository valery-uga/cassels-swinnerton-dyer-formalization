import PfaffianDescent.PointCartierYonedaSourceComparison
import PfaffianDescent.PointCartierYonedaPointQuotientIso
import PfaffianDescent.PointCartierYonedaAmbientNonzero

/-! # Local Cartier/Yoneda comparison at a regular point

This file collects a bounded local algebraic comparison. The actual
two-parameter surface Koszul generator, restricted to the ambient ring and
transported through the canonical point quotient isomorphism, has Cartier
boundary equal to the ambient three-parameter class with unit coefficient.
No global sheaf or trace compatibility is asserted here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u w w'

variable {R : Type u} [CommRing R]
variable (f g h p : R) (v : Rˣ) (b c : R)
variable (heq : p = f * (v : R) + g * b + h * c) (hf : f ∈ R⁰)
variable (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
variable (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
  x ∈ Ideal.span ({f, g} : Set R))
variable (hgB : Ideal.Quotient.mk (Ideal.span {p}) g ∈ (R ⧸ Ideal.span {p})⁰)
variable (hhB : Ideal.Quotient.mk
  (Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) g})
  (Ideal.Quotient.mk (Ideal.span {p}) h) ∈
    ((R ⧸ Ideal.span {p}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) g})⁰)

/-- The source map of the bounded comparison is the canonical point
quotient isomorphism, not an additional compatibility hypothesis. -/
theorem pointCartierYonedaSourceComparison_onP_isIso :
    IsIso (pointCartierYonedaSourceComparison f g h p v b c heq hf hg hh hgB hhB).onP := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (pointCartierYonedaPointQuotientMap f g h p v b c heq)
  exact pointCartierYonedaPointQuotientMap_bijective f g h p v b c heq

/-- The local Cartier Yoneda boundary of the actual surface generator is
nonzero when the ambient point ideal is proper. -/
theorem pointCartierYoneda_surface_generator_boundary_ne_zero
    [hExt : HasExt.{w} (ModuleCat R)]
    [hExtB : HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {p}))]
    (hp : p ∈ R⁰) (hproper : Ideal.span ({f, g, h} : Set R) ≠ ⊤) :
    ((Ext.mk₀ (pointCartierYonedaSourceComparison f g h p v b c heq hf hg hh hgB hhB).onP).comp
      ((localSerreExtTwoClass (Ideal.Quotient.mk (Ideal.span {p}) g)
        (Ideal.Quotient.mk (Ideal.span {p}) h) 1 hgB hhB).mapExactFunctor
          (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {p})))) (zero_add 2)).comp
      (pointCartierYonedaCoefficientComplex_shortExact p hp).extClass
      (show 2 + 1 = 3 by rfl) ≠ 0 := by
  rw [pointCartierYoneda_surface_generator_boundary f g h p v b c heq hp hf hg hh hgB hhB]
  exact pointCartierYonedaAmbientClass_unit_ne_zero f g h hf hg hh v⁻¹ hproper

end PfaffianDescent

import PfaffianDescent.ActualIdealStalkDualPrincipalSequence190
import PfaffianDescent.FirstCartierPrincipalParameter188

/-! SOURCE ONLY / UNCHECKED. Bounded first-Cartier comparison for the
actual inclusion functional, followed by the literal second Cartier map.
The coefficient-one two-parameter class and the quotient augmentation are
conclusions. This is local ModuleCat algebra, not a global trace assertion. -/
noncomputable section
set_option autoImplicit false
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
universe u w w'

/-- A frame of the actual ideal with its ordinary parameter action gives
the coefficient-one two-Cartier class. No extension-class comparison or
boundary/trace normalization is a premise. The actual quotient projection
is retained on the right side of the augmentation square. -/
theorem actualIdealFrameDualIncrement_twoCartier_coefficientOne190
    {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat R)]
    (f g : R) [HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {f}))]
    (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    {M : Type u} [AddCommGroup M] [Module (R ⧸ Ideal.span {f}) M]
    (e : (R ⧸ Ideal.span {f}) ≃ₗ[R ⧸ Ideal.span {f}] M)
    (j : M →ₗ[R ⧸ Ideal.span {f}] (R ⧸ Ideal.span {f}))
    (he : ∀ r, j (e r) = r * Ideal.Quotient.mk (Ideal.span {f}) g) :
    let q := Ideal.Quotient.mk (Ideal.span {f})
    let F := ModuleCat.restrictScalars q
    let S := actualIdealFrameDualIncrement190 e j (q g) he
    ∃ kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ F.obj S.X₃,
      (localSerreIdealQuotientComplex f g).g ≫ kappa =
        (pointCartierYonedaCoefficientComplex f).g ≫
          F.map ((actualIdealFrameDualCoordinate190 e).toModuleIso.inv ≫ S.g) ∧
      ((Ext.mk₀ kappa).comp
          ((actualIdealFrameDualIncrement_shortExact190 e j (q g) he hg).extClass.mapExactFunctor F)
          (zero_add 1)).comp
        (pointCartierYonedaCoefficientComplex_shortExact f hf).extClass
        (show 1 + 1 = 2 by rfl) = localSerreExtTwoClass f g 1 hf hg := by
  let q := Ideal.Quotient.mk (Ideal.span {f})
  let F := ModuleCat.restrictScalars q
  let S := actualIdealFrameDualIncrement190 e j (q g) he
  obtain ⟨kappa, hk, hc⟩ := firstCartierPrincipalParameter_boundary188 f g hf hg
  refine ⟨kappa, ?_, ?_⟩
  · change (localSerreIdealQuotientComplex f g).g ≫ kappa =
      (pointCartierYonedaCoefficientComplex f).g ≫
        F.map ((actualIdealFrameDualCoordinate190 e).toModuleIso.inv ≫
          (actualIdealFrameDualIncrement190 e j (q g) he).g)
    rw [actualIdealFrameDualIncrement_inverse_projection190 e j (q g) he]
    exact hk
  · change ((Ext.mk₀ kappa).comp
        ((actualIdealFrameDualIncrement_shortExact190 e j (q g) he hg).extClass.mapExactFunctor F)
        (zero_add 1)).comp
      (pointCartierYonedaCoefficientComplex_shortExact f hf).extClass
      (show 1 + 1 = 2 by rfl) = _
    rw [actualIdealFrameDualIncrement_extClass190 e j (q g) he hg]
    exact hc

end PfaffianDescent

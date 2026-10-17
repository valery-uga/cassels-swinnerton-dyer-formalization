import PfaffianDescent.WholeQuotientPointCoefficient202
import PfaffianDescent.WholeExactRestrictionClassTransport202

/-! The coefficient-one class with the actual original restriction scalar
map, rather than a substituted action. Every comparison is constructed. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
universe u w w'
set_option backward.isDefEq.respectTransparency false

theorem wholePoint_originalRestriction_firstCartier_coefficientOne202
    {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing B]
    [HasExt.{w} (ModuleCat R)]
    (f : R) [HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {f}))] (hf : f ∈ R⁰)
    (e : (R ⧸ Ideal.span {f}) ≃+* B)
    (phi : R →+* B) (hphi : phi = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {f})))
    (W : ShortComplex (ModuleCat B)) (hW : W.ShortExact)
    (t : B) (ht : t ∈ B⁰) (hmem : t ∈ IsLocalRing.maximalIdeal B)
    (a : W ≅ pointCartierYonedaCoefficientComplex t) :
    let q := Ideal.Quotient.mk (Ideal.span {f})
    let Q := ModuleCat.restrictScalars q
    let E := ModuleCat.restrictScalars e.toRingHom
    let V := W.map E
    let Phi := ModuleCat.restrictScalars phi
    let eta := ModuleCat.restrictScalarsComp' q e.toRingHom phi hphi
    let aC := quotientWholePrincipalIso202 f e W t ht a
    let e₁ := (ShortComplex.π₁ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
    let e₂ := (ShortComplex.π₂ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
    ∃ g : R, phi g = t ∧
      ∃ hg : q g ∈ (R ⧸ Ideal.span {f})⁰,
      ∃ kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ Phi.obj W.X₃,
        (localSerreIdealQuotientComplex f g).g ≫ kappa =
          (pointCartierYonedaCoefficientComplex f).g ≫
            ((Q.map e₂.inv ≫ (eta.app W.X₂).inv) ≫ Phi.map W.g) ∧
        ((Ext.mk₀ kappa).comp
            ((hW.map_of_exact Phi).extClass.comp
              (Ext.mk₀ ((eta.app W.X₁).hom ≫ Q.map e₁.hom)) (add_zero 1))
            (zero_add 1)).comp
          (pointCartierYonedaCoefficientComplex_shortExact f hf).extClass
          (show 1 + 1 = 2 by rfl) = localSerreExtTwoClass f g 1 hf hg ∧
        localSerreExtTwoClass f g 1 hf hg ≠ 0 := by
  dsimp only
  let q := Ideal.Quotient.mk (Ideal.span {f})
  let Q := ModuleCat.restrictScalars q
  let E := ModuleCat.restrictScalars e.toRingHom
  let V := W.map E
  let Phi := ModuleCat.restrictScalars phi
  let eta := ModuleCat.restrictScalarsComp' q e.toRingHom phi hphi
  let aC := quotientWholePrincipalIso202 f e W t ht a
  let e₁ := (ShortComplex.π₁ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
  let e₂ := (ShortComplex.π₂ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
  obtain ⟨g, hg, hg0, kappa₀, hprojection, hclass, hnonzero⟩ :=
    quotientWholePoint_firstCartier_coefficientOne202 f hf e W hW t ht hmem a
  have hgt : phi g = t := by rw [hphi]; exact hg
  let kappa := kappa₀ ≫ (eta.app W.X₃).inv
  refine ⟨g, hgt, hg0, kappa, ?_, ?_, hnonzero⟩
  · change (localSerreIdealQuotientComplex f g).g ≫
        (kappa₀ ≫ (eta.app W.X₃).inv) = _
    rw [← Category.assoc, hprojection, Q.map_comp, Category.assoc]
    exact congrArg (fun b => (pointCartierYonedaCoefficientComplex f).g ≫ b)
      (wholeExactNaturalIso_projection202 Phi (E ⋙ Q) eta W.X₂ W.X₃ W.g
        _ (Q.map e₂.inv)).symm
  · rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
      Ext.mapExactFunctor_mk₀] at hclass
    have htransport := wholeExactNaturalIso_normalizedClass202 Phi (E ⋙ Q) eta W hW
      _ _ kappa₀ (Q.map e₁.hom)
    change ((Ext.mk₀ kappa).comp
        ((hW.map_of_exact Phi).extClass.comp
          (Ext.mk₀ ((eta.app W.X₁).hom ≫ Q.map e₁.hom)) (add_zero 1))
        (zero_add 1)).comp
      (pointCartierYonedaCoefficientComplex_shortExact f hf).extClass
      (show 1 + 1 = 2 by rfl) = _
    rw [htransport]
    exact hclass

end PfaffianDescent

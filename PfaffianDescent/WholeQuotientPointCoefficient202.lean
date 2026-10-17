import PfaffianDescent.WholePrincipalIsoCoefficient202
import PfaffianDescent.PrincipalRingEquivWholeSequence199
import PfaffianDescent.LocalSerreExtensionPresentation

/-! Transport an actual WHOLE point extension from the original ring B
through the actual principal surface quotient. Its cokernel is retained. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
universe u w w'
set_option backward.isDefEq.respectTransparency false

/-- The entire original sequence is transported, including its third
component. The parameter comparison is derived from ring-equivalence transport. -/
def quotientWholePrincipalIso202
    {R B : Type u} [CommRing R] [CommRing B]
    (f : R) (e : (R ⧸ Ideal.span {f}) ≃+* B)
    (W : ShortComplex (ModuleCat B)) (t : B) (ht : t ∈ B⁰)
    (a : W ≅ pointCartierYonedaCoefficientComplex t) :
    W.map (ModuleCat.restrictScalars e.toRingHom) ≅
      pointCartierYonedaCoefficientComplex (e.symm t) :=
  (ModuleCat.restrictScalars e.toRingHom).mapShortComplex.mapIso a ≪≫
    principalRingEquivWholeSequenceIso199 e t ht

lemma quotientWholePrincipalIso_first_hom202
    {R B : Type u} [CommRing R] [CommRing B]
    (f : R) (e : (R ⧸ Ideal.span {f}) ≃+* B)
    (W : ShortComplex (ModuleCat B)) (t : B) (ht : t ∈ B⁰)
    (a : W ≅ pointCartierYonedaCoefficientComplex t) :
    (quotientWholePrincipalIso202 f e W t ht a).hom.τ₁ =
      (ModuleCat.restrictScalars e.toRingHom).map a.hom.τ₁ ≫
        (ModuleCat.restrictScalarsIsoOfEquiv e).hom := rfl

lemma quotientWholePrincipalIso_second_inv202
    {R B : Type u} [CommRing R] [CommRing B]
    (f : R) (e : (R ⧸ Ideal.span {f}) ≃+* B)
    (W : ShortComplex (ModuleCat B)) (t : B) (ht : t ∈ B⁰)
    (a : W ≅ pointCartierYonedaCoefficientComplex t) :
    (quotientWholePrincipalIso202 f e W t ht a).inv.τ₂ =
      (ModuleCat.restrictScalarsIsoOfEquiv e).inv ≫
        (ModuleCat.restrictScalars e.toRingHom).map a.inv.τ₂ := rfl

/-- This uses the ORIGINAL W.X3 and original W.g. Properness and local
coefficient-one nonvanishing follow from the original point maximal ideal.
No class-comparison or nonzero premise is assumed. The geometric caller
constructs e and a from196 and200; they are ordinary generic transport data. -/
theorem quotientWholePoint_firstCartier_coefficientOne202
    {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing B]
    [HasExt.{w} (ModuleCat R)]
    (f : R) [HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {f}))] (hf : f ∈ R⁰)
    (e : (R ⧸ Ideal.span {f}) ≃+* B)
    (W : ShortComplex (ModuleCat B)) (hW : W.ShortExact)
    (t : B) (ht : t ∈ B⁰) (hmem : t ∈ IsLocalRing.maximalIdeal B)
    (a : W ≅ pointCartierYonedaCoefficientComplex t) :
    let q := Ideal.Quotient.mk (Ideal.span {f})
    let Q := ModuleCat.restrictScalars q
    let E := ModuleCat.restrictScalars e.toRingHom
    let V := W.map E
    let hV := hW.map_of_exact E
    let aC := quotientWholePrincipalIso202 f e W t ht a
    let e₁ := (ShortComplex.π₁ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
    let e₂ := (ShortComplex.π₂ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
    ∃ g : R, e (q g) = t ∧
      ∃ hg : q g ∈ (R ⧸ Ideal.span {f})⁰,
      ∃ kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ Q.obj V.X₃,
        (localSerreIdealQuotientComplex f g).g ≫ kappa =
          (pointCartierYonedaCoefficientComplex f).g ≫ Q.map (e₂.inv ≫ V.g) ∧
        ((Ext.mk₀ kappa).comp
            ((hV.extClass.comp (Ext.mk₀ e₁.hom) (add_zero 1)).mapExactFunctor Q)
            (zero_add 1)).comp
          (pointCartierYonedaCoefficientComplex_shortExact f hf).extClass
          (show 1 + 1 = 2 by rfl) = localSerreExtTwoClass f g 1 hf hg ∧
        localSerreExtTwoClass f g 1 hf hg ≠ 0 := by
  dsimp only
  let E := ModuleCat.restrictScalars e.toRingHom
  let V := W.map E
  let aC := quotientWholePrincipalIso202 f e W t ht a
  obtain ⟨g, hg, hg0, kappa, hprojection, hclass⟩ :=
    wholePrincipalIso_firstCartier_coefficientOne202 f hf V
      (hW.map_of_exact E) (e.symm t) aC
  have hgt : e (Ideal.Quotient.mk _ g) = t := by
    rw [hg, e.apply_symm_apply]
  have hmg : e (Ideal.Quotient.mk _ g) ∈ IsLocalRing.maximalIdeal B := by
    rw [hgt]
    exact hmem
  refine ⟨g, hgt, hg0, kappa, hprojection, hclass, ?_⟩
  exact localSerreExtTwoClass_one_ne_zero_of_one_not_mem_span f g hf hg0
    (principalRingEquiv_lift_pair_one_not_mem_span199 f g e hmg)

end PfaffianDescent

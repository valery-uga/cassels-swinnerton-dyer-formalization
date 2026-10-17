import PfaffianDescent.WholeQuotientPointCoefficient202

/-! SOURCE ONLY213.202's actual augmentation projection determines its
coefficient on EVERY ring lift through the entire original principal complex. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary202 construction data determine the augmentation's original
principal quotient value. No coefficient/augmentation comparison is assumed. -/
theorem wholeOriginalRestrictionAugmentation_principalValue213
    {R B : Type u} [CommRing R] [CommRing B]
    (f g : R) (e : (R ⧸ Ideal.span {f}) ≃+* B)
    (phi : R →+* B) (hphi : phi = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {f})))
    (W : ShortComplex (ModuleCat B)) (t : B) (ht : t ∈ B⁰)
    (a : W ≅ pointCartierYonedaCoefficientComplex t) :
    let q := Ideal.Quotient.mk (Ideal.span {f})
    let Q := ModuleCat.restrictScalars q
    let Phi := ModuleCat.restrictScalars phi
    let eta := ModuleCat.restrictScalarsComp' q e.toRingHom phi hphi
    let aC := quotientWholePrincipalIso202 f e W t ht a
    let e₂ := (ShortComplex.π₂ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso aC
    ∀ (kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ Phi.obj W.X₃),
      (localSerreIdealQuotientComplex f g).g ≫ kappa =
        (pointCartierYonedaCoefficientComplex f).g ≫
          ((Q.map e₂.inv ≫ (eta.app W.X₂).inv) ≫ Phi.map W.g) →
      ∀ r : R, a.hom.τ₃ (kappa (Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) r)) =
        Ideal.Quotient.mk (Ideal.span ({t} : Set B)) (phi r) := by
  dsimp only
  intro kappa hProjection r
  have hValue := ConcreteCategory.congr_hom hProjection r
  dsimp only [Functor.mapIso_inv, ShortComplex.π₂] at hValue
  rw [quotientWholePrincipalIso_second_inv202] at hValue
  change kappa (Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) r) =
    W.g (a.inv.τ₂ (e (Ideal.Quotient.mk (Ideal.span {f}) r))) at hValue
  have hphiValue : phi r = e (Ideal.Quotient.mk (Ideal.span {f}) r) :=
    congrArg (fun h : R →+* B => h r) hphi
  rw [← hphiValue] at hValue
  have hComm := ConcreteCategory.congr_hom a.inv.comm₂₃ (phi r)
  change W.g (a.inv.τ₂ (phi r)) =
    a.inv.τ₃ (Ideal.Quotient.mk (Ideal.span ({t} : Set B)) (phi r)) at hComm
  rw [hValue, hComm]
  exact ConcreteCategory.congr_hom
    ((ShortComplex.π₃ : ShortComplex (ModuleCat B) ⥤ _).mapIso a).inv_hom_id _

end PfaffianDescent

import PfaffianDescent.WholePrincipalFirstCartierTransport199

/-! A whole principal isomorphism determines the actual scalar of a
sequence, then the coefficient-one augmentation into its ORIGINAL cokernel. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
universe u w w'
set_option backward.isDefEq.respectTransparency false

lemma wholePrincipalIso_scalar202
    {C : Type u} [CommRing C]
    (V : ShortComplex (ModuleCat C)) (t : C)
    (a : V ≅ pointCartierYonedaCoefficientComplex t) :
    pointCartierNativeStalkScalar V
      ((ShortComplex.π₁ : ShortComplex (ModuleCat C) ⥤ ModuleCat C).mapIso a)
      ((ShortComplex.π₂ : ShortComplex (ModuleCat C) ⥤ ModuleCat C).mapIso a) = t := by
  let e₁ : V.X₁ ≅ ModuleCat.of C C :=
    (ShortComplex.π₁ : ShortComplex (ModuleCat C) ⥤ ModuleCat C).mapIso a
  let e₂ : V.X₂ ≅ ModuleCat.of C C :=
    (ShortComplex.π₂ : ShortComplex (ModuleCat C) ⥤ ModuleCat C).mapIso a
  have hc : e₁.inv ≫ V.f ≫ e₂.hom = (pointCartierYonedaCoefficientComplex t).f := by
    calc
      _ = e₁.inv ≫ (e₁.hom ≫ (pointCartierYonedaCoefficientComplex t).f) :=
        congrArg (fun h => e₁.inv ≫ h) a.hom.comm₁₂.symm
      _ = _ := e₁.inv_hom_id_assoc _
  change (e₁.inv ≫ V.f ≫ e₂.hom).hom (1 : C) = t
  rw [hc]
  change t * 1 = t
  exact mul_one t

/-- No class identity is input. The whole sequence Iso and its actual
first/middle coordinates determine the parameter and the original projection. -/
theorem wholePrincipalIso_firstCartier_coefficientOne202
    {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat R)]
    (f : R) [HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {f}))] (hf : f ∈ R⁰)
    (V : ShortComplex (ModuleCat (R ⧸ Ideal.span {f}))) (hV : V.ShortExact)
    (t : R ⧸ Ideal.span {f}) (a : V ≅ pointCartierYonedaCoefficientComplex t) :
    let q := Ideal.Quotient.mk (Ideal.span {f})
    let F := ModuleCat.restrictScalars q
    let e₁ := (ShortComplex.π₁ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso a
    let e₂ := (ShortComplex.π₂ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso a
    ∃ g : R, q g = t ∧
      ∃ hg : q g ∈ (R ⧸ Ideal.span {f})⁰,
      ∃ kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ F.obj V.X₃,
        (localSerreIdealQuotientComplex f g).g ≫ kappa =
          (pointCartierYonedaCoefficientComplex f).g ≫ F.map (e₂.inv ≫ V.g) ∧
        ((Ext.mk₀ kappa).comp
            ((hV.extClass.comp (Ext.mk₀ e₁.hom) (add_zero 1)).mapExactFunctor F)
            (zero_add 1)).comp
          (pointCartierYonedaCoefficientComplex_shortExact f hf).extClass
          (show 1 + 1 = 2 by rfl) = localSerreExtTwoClass f g 1 hf hg := by
  dsimp only
  obtain ⟨g, hg, hreg, kappa, hprojection, hclass⟩ :=
    wholePrincipalSequence_firstCartier_coefficientOne199 f hf V hV
      ((ShortComplex.π₁ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso a)
      ((ShortComplex.π₂ : ShortComplex (ModuleCat (R ⧸ Ideal.span {f})) ⥤ _).mapIso a)
  rw [wholePrincipalIso_scalar202 V t a] at hg
  exact ⟨g, hg, hreg, kappa, hprojection, hclass⟩

end PfaffianDescent

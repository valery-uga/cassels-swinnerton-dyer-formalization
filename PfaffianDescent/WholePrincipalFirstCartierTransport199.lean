import PfaffianDescent.FirstCartierPrincipalParameter188
import PfaffianDescent.PointCartierNativeStalkPrincipalNormalization

/-! A whole actual rank-one extension over the literal principal quotient
has a coefficient-one first-Cartier boundary. Its original endpoint and
projection are retained; the lifted second parameter is constructed. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
universe u w w'
set_option backward.isDefEq.respectTransparency false

/-- Ordinary sequence coordinates, with no class-comparison premise, yield
an actual lifted parameter and the entire original quotient augmentation. -/
theorem wholePrincipalSequence_firstCartier_coefficientOne199
    {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat R)]
    (f : R) [HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {f}))] (hf : f ∈ R⁰)
    (V : ShortComplex (ModuleCat (R ⧸ Ideal.span {f}))) (hV : V.ShortExact)
    (e₁ : V.X₁ ≅ ModuleCat.of (R ⧸ Ideal.span {f}) (R ⧸ Ideal.span {f}))
    (e₂ : V.X₂ ≅ ModuleCat.of (R ⧸ Ideal.span {f}) (R ⧸ Ideal.span {f})) :
    let q := Ideal.Quotient.mk (Ideal.span {f})
    let F := ModuleCat.restrictScalars q
    ∃ g : R, q g = pointCartierNativeStalkScalar V e₁ e₂ ∧
      ∃ hg : q g ∈ (R ⧸ Ideal.span {f})⁰,
      ∃ kappa : ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) ⟶ F.obj V.X₃,
        (localSerreIdealQuotientComplex f g).g ≫ kappa =
          (pointCartierYonedaCoefficientComplex f).g ≫ F.map (e₂.inv ≫ V.g) ∧
        ((Ext.mk₀ kappa).comp
            ((hV.extClass.comp (Ext.mk₀ e₁.hom) (add_zero 1)).mapExactFunctor F)
            (zero_add 1)).comp
          (pointCartierYonedaCoefficientComplex_shortExact f hf).extClass
          (show 1 + 1 = 2 by rfl) = localSerreExtTwoClass f g 1 hf hg := by
  let q := Ideal.Quotient.mk (Ideal.span {f})
  let F := ModuleCat.restrictScalars q
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
    (pointCartierNativeStalkScalar V e₁ e₂)
  have hg0 : q g ∈ (R ⧸ Ideal.span {f})⁰ := by
    rw [hg]
    exact pointCartierNativeStalkScalar_regular V hV e₁ e₂
  let T := pointCartierYonedaCoefficientComplex (q g)
  let hT := pointCartierYonedaCoefficientComplex_shortExact (q g) hg0
  have hfirst : V.f ≫ e₂.hom = e₁.hom ≫ T.f := by
    change V.f ≫ e₂.hom = e₁.hom ≫ (pointCartierYonedaCoefficientComplex (q g)).f
    rw [hg]
    exact pointCartierNativeStalkPrincipal_square V e₁ e₂
  let d : V ≅ T := ShortComplex.isoMk e₁ e₂
    (pointCartierNativeStalkCokernelIso V T hV hT e₁ e₂ hfirst)
    hfirst.symm
    (pointCartierNativeStalkCokernelIso_square V T hV hT e₁ e₂ hfirst).symm
  have hd₁ : d.inv.τ₁ = e₁.inv := rfl
  have hd₂ : d.inv.τ₂ = e₂.inv := rfl
  obtain ⟨kappa₀, hk₀, hc₀⟩ := firstCartierPrincipalParameter_boundary188 f g hf hg0
  let kappa := kappa₀ ≫ F.map d.inv.τ₃
  refine ⟨g, hg, hg0, kappa, ?_, ?_⟩
  · change (localSerreIdealQuotientComplex f g).g ≫
      (kappa₀ ≫ F.map d.inv.τ₃) = _
    rw [← Category.assoc, hk₀, Category.assoc, ← F.map_comp,
      ← d.inv.comm₂₃, hd₂]
  · have hn := hT.extClass_naturality hV d.inv
    rw [hd₁] at hn
    have hn' : (Ext.mk₀ d.inv.τ₃).comp
        (hV.extClass.comp (Ext.mk₀ e₁.hom) (add_zero 1)) (zero_add 1) =
        hT.extClass := by
      calc
        _ = ((Ext.mk₀ d.inv.τ₃).comp hV.extClass (zero_add 1)).comp
            (Ext.mk₀ e₁.hom) (add_zero 1) :=
          (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add 1)).symm
        _ = (hT.extClass.comp (Ext.mk₀ e₁.inv) (add_zero 1)).comp
            (Ext.mk₀ e₁.hom) (add_zero 1) := by rw [← hn]
        _ = hT.extClass.comp
            ((Ext.mk₀ e₁.inv).comp (Ext.mk₀ e₁.hom) (zero_add 0))
            (add_zero 1) := Ext.comp_assoc_of_second_deg_zero _ _ _ (add_zero 1)
        _ = hT.extClass := by
          rw [Ext.mk₀_comp_mk₀, Iso.inv_hom_id]
          change hT.extClass.comp (Ext.mk₀ (𝟙 T.X₁)) (add_zero 1) = hT.extClass
          exact Ext.comp_mk₀_id hT.extClass
    change ((Ext.mk₀ (kappa₀ ≫ F.map d.inv.τ₃)).comp
        ((hV.extClass.comp (Ext.mk₀ e₁.hom) (add_zero 1)).mapExactFunctor F)
        (zero_add 1)).comp
      (pointCartierYonedaCoefficientComplex_shortExact f hf).extClass
      (show 1 + 1 = 2 by rfl) = _
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      ← Ext.mapExactFunctor_mk₀, ← Ext.mapExactFunctor_comp, hn']
    exact hc₀

end PfaffianDescent

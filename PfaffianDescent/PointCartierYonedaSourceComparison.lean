import PfaffianDescent.PointCartierYonedaUnitBoundary
import PfaffianDescent.PointCartierYonedaPointQuotient

/-! # Yoneda source comparison with the actual surface Koszul generator

The explicit unit-normalized maps form a comparison from the ambient point
resolution to the restriction of the surface two-parameter resolution.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u w w'

variable {R : Type u} [CommRing R]

def pointCartierYonedaSourceComparison (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R))
    (hgB : Ideal.Quotient.mk (Ideal.span {p}) g ∈ (R ⧸ Ideal.span {p})⁰)
    (hhB : Ideal.Quotient.mk
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) g})
      (Ideal.Quotient.mk (Ideal.span {p}) h) ∈
        ((R ⧸ Ideal.span {p}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) g})⁰) :
    TwoStepResolution.Hom
      (pointCartierYonedaAmbientResolution f g h hf hg hh).toTwoStep
      ((pointCartierYonedaSurfaceResolution
        (Ideal.Quotient.mk (Ideal.span {p}) g) (Ideal.Quotient.mk (Ideal.span {p}) h) hgB hhB).map
          (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {p})))) := by
  apply TwoStepResolution.Hom.ofFirstTerms
    (ModuleCat.ofHom (pointCartierYonedaPointQuotientMap f g h p v b c heq))
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap)
    (ModuleCat.ofHom (pointCartierYonedaUnitRetractionOne p v b c))
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · change (Abelian.factorThruImage (ModuleCat.ofHom (threeGeneratorLast f g h)) ≫
      Abelian.image.ι (ModuleCat.ofHom (threeGeneratorLast f g h))) ≫ _ = _
    rw [Abelian.image.fac]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Ideal.Quotient.mk (Ideal.span {p}) (threeGeneratorLast f g h x) =
      localKoszulGeneratorMap (Ideal.Quotient.mk (Ideal.span {p}) g)
        (Ideal.Quotient.mk (Ideal.span {p}) h) (pointCartierYonedaUnitRetractionOne p v b c x)
    exact (pointCartierYonedaUnitRetraction_last f g h p v b c heq x).symm

theorem pointCartierYonedaUnitTwoClass_eq_surface_class
    [hExt : HasExt.{w} (ModuleCat R)]
    (f g h p : R) [hExtB : HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {p}))]
    (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R))
    (hgB : Ideal.Quotient.mk (Ideal.span {p}) g ∈ (R ⧸ Ideal.span {p})⁰)
    (hhB : Ideal.Quotient.mk
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) g})
      (Ideal.Quotient.mk (Ideal.span {p}) h) ∈
        ((R ⧸ Ideal.span {p}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) g})⁰) :
    pointCartierYonedaUnitTwoClass f g h p v b c heq hf hg hh =
      (Ext.mk₀ (pointCartierYonedaSourceComparison f g h p v b c heq hf hg hh hgB hhB).onP).comp
        ((localSerreExtTwoClass (Ideal.Quotient.mk (Ideal.span {p}) g)
          (Ideal.Quotient.mk (Ideal.span {p}) h) 1 hgB hhB).mapExactFunctor
            (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {p})))) (zero_add 2) := by
  let T := pointCartierYonedaAmbientResolution f g h hf hg hh
  let U := pointCartierYonedaSurfaceResolution
    (Ideal.Quotient.mk (Ideal.span {p}) g) (Ideal.Quotient.mk (Ideal.span {p}) h) hgB hhB
  let F := ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {p}))
  let φ := pointCartierYonedaSourceComparison f g h p v b c heq hf hg hh hgB hhB
  let π : T.C₂ ⟶ T.K₁ := Abelian.coimage.π (ModuleCat.ofHom (threeGeneratorMiddle f g h))
  let r : T.K₁ ⟶ ModuleCat.of R (R ⧸ Ideal.span {p}) :=
    degreeTwoCocycleDesc (ModuleCat.ofHom (threeGeneratorMiddle f g h))
      (ModuleCat.ofHom (threeGeneratorFirst f g h))
      (pointCartierYonedaAmbientMiddle_zero f g h)
      (pointCartierYonedaAmbientMiddle_exact f g h hf hg)
      (pointCartierYonedaUnitTwoCocycle f g h p v b c heq)
  let a : T.C₂ ⟶ (U.map F).K₁ := by
    change ModuleCat.of R (R × R × R) ⟶ ModuleCat.of R (R ⧸ Ideal.span {p})
    exact ModuleCat.ofHom (pointCartierYonedaUnitCocycleMap p v b c)
  let s : (U.map F).K₁ ⟶ ModuleCat.of R (R ⧸ Ideal.span {p}) :=
    F.map (ModuleCat.ofHom (LinearMap.lsmul (R ⧸ Ideal.span {p}) (R ⧸ Ideal.span {p}) 1))
  have hrelation : (π ≫ T.toTwoStep.i₁) ≫ φ.onC₁ = a ≫ ((𝟙 _) ≫ (U.map F).i₁) := by
    change (Abelian.coimage.π (ModuleCat.ofHom (threeGeneratorMiddle f g h)) ≫
      Abelian.factorThruCoimage (ModuleCat.ofHom (threeGeneratorMiddle f g h))) ≫
        ModuleCat.ofHom (pointCartierYonedaUnitRetractionOne p v b c) = _
    rw [Abelian.coimage.fac]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change pointCartierYonedaUnitRetractionOne p v b c (threeGeneratorMiddle f g h x) =
      localKoszulRelationMap (Ideal.Quotient.mk (Ideal.span {p}) g)
        (Ideal.Quotient.mk (Ideal.span {p}) h) (pointCartierYonedaUnitCocycleMap p v b c x)
    exact pointCartierYonedaUnitRetraction_middle f g h p v b c heq x
  have hcoeff : π ≫ r = a ≫ ((𝟙 _) ≫ s) := by
    change Abelian.coimage.π (ModuleCat.ofHom (threeGeneratorMiddle f g h)) ≫
      degreeTwoCocycleDesc _ _ _ _ _ = _
    rw [coimage_π_comp_degreeTwoCocycleDesc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change pointCartierYonedaUnitCocycleMap p v b c x =
      (1 : R ⧸ Ideal.span {p}) * pointCartierYonedaUnitCocycleMap p v b c x
    exact (one_mul _).symm
  letI : Epi π := by dsimp [π]; infer_instance
  have hn := TwoStepResolution.connecting_naturality_of_coefficients φ π (𝟙 _) a
    hrelation r s hcoeff
  have hm := U.connecting_map F (ModuleCat.of (R ⧸ Ideal.span {p}) (R ⧸ Ideal.span {p}))
    (ModuleCat.ofHom (LinearMap.lsmul (R ⧸ Ideal.span {p}) (R ⧸ Ideal.span {p}) 1))
  rw [pointCartierYonedaSurfaceResolution_connecting] at hm
  change (localSerreExtTwoClass (Ideal.Quotient.mk (Ideal.span {p}) g)
    (Ideal.Quotient.mk (Ideal.span {p}) h) 1 hgB hhB).mapExactFunctor F =
      (U.map F).connecting (ModuleCat.of R (R ⧸ Ideal.span {p})) s at hm
  change T.toTwoStep.connecting (ModuleCat.of R (R ⧸ Ideal.span {p})) r =
    (Ext.mk₀ φ.onP).comp ((U.map F).connecting (ModuleCat.of R (R ⧸ Ideal.span {p})) s)
      (zero_add 2) at hn
  rw [← hm] at hn
  exact hn

/-- The restricted actual surface Koszul generator, pulled back along the
canonical point augmentation, has Cartier Yoneda boundary equal to the
ambient point class with coefficient `v⁻¹`. -/
theorem pointCartierYoneda_surface_generator_boundary
    [hExt : HasExt.{w} (ModuleCat R)]
    (f g h p : R) [hExtB : HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {p}))]
    (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) (hp : p ∈ R⁰) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R))
    (hgB : Ideal.Quotient.mk (Ideal.span {p}) g ∈ (R ⧸ Ideal.span {p})⁰)
    (hhB : Ideal.Quotient.mk
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) g})
      (Ideal.Quotient.mk (Ideal.span {p}) h) ∈
        ((R ⧸ Ideal.span {p}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {p}) g})⁰) :
    ((Ext.mk₀ (pointCartierYonedaSourceComparison f g h p v b c heq hf hg hh hgB hhB).onP).comp
      ((localSerreExtTwoClass (Ideal.Quotient.mk (Ideal.span {p}) g)
        (Ideal.Quotient.mk (Ideal.span {p}) h) 1 hgB hhB).mapExactFunctor
          (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {p})))) (zero_add 2)).comp
      (pointCartierYonedaCoefficientComplex_shortExact p hp).extClass
      (show 2 + 1 = 3 by rfl) =
        pointCartierYonedaAmbientClass f g h hf hg hh (v⁻¹ : Rˣ) := by
  rw [← pointCartierYonedaUnitTwoClass_eq_surface_class f g h p v b c heq hf hg hh hgB hhB]
  exact pointCartierYonedaUnitTwoClass_boundary f g h p v b c heq hp hf hg hh

end PfaffianDescent

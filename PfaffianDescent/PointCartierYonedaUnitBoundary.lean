import PfaffianDescent.PointCartierYonedaCocycleBoundary
import PfaffianDescent.PointCartierYonedaAmbientKoszul
import PfaffianDescent.PointCartierYonedaUnitLift

/-! # Actual Cartier Yoneda boundary of the unit-normalized cocycle

The degree-two class on the ambient point resolution with coefficients in
the Cartier quotient is composed with the actual principal coefficient
extension. The resulting degree-three class has coefficient `v⁻¹`.
This statement computes an actual Yoneda product in the ambient module
category. It does not identify any global trace map.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u w

variable {R : Type u} [CommRing R] [hExt : HasExt.{w} (ModuleCat R)]

def pointCartierYonedaUnitTwoCocycle (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) :
    DegreeTwoCocycle (ModuleCat.ofHom (threeGeneratorFirst f g h))
      (Y := ModuleCat.of R (R ⧸ Ideal.span {p})) :=
  ⟨ModuleCat.ofHom (pointCartierYonedaUnitCocycleMap p v b c), by
    apply ModuleCat.hom_ext
    exact pointCartierYonedaUnitCocycleMap_comp_first f g h p v b c heq⟩

def pointCartierYonedaAmbientTopCocycle (r : R) :
    DegreeThreeCocycle (0 : ModuleCat.of R PUnit ⟶ ModuleCat.of R R)
      (Y := ModuleCat.of R R) :=
  ⟨ModuleCat.ofHom (LinearMap.lsmul R R r), by
    change (0 : ModuleCat.of R PUnit ⟶ ModuleCat.of R R) ≫ _ = 0
    simp⟩

def pointCartierYonedaAmbientClass (f g h : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) (r : R) :
    Ext.{w} (pointCartierYonedaAmbientPoint f g h) (ModuleCat.of R R) 3 :=
  (pointCartierYonedaAmbientResolution f g h hf hg hh).connecting (ModuleCat.of R R)
    (degreeThreeCocycleDesc (ModuleCat.ofHom (threeGeneratorFirst f g h))
      (0 : ModuleCat.of R PUnit ⟶ ModuleCat.of R R) (by simp)
      (pointCartierYonedaAmbientFirst_exact f g h hf)
      (pointCartierYonedaAmbientTopCocycle r))

def pointCartierYonedaUnitTwoClass (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) :
    Ext.{w} (pointCartierYonedaAmbientPoint f g h)
      (ModuleCat.of R (R ⧸ Ideal.span {p})) 2 :=
  (pointCartierYonedaAmbientResolution f g h hf hg hh).toTwoStep.connecting
    (ModuleCat.of R (R ⧸ Ideal.span {p}))
    (degreeTwoCocycleDesc (ModuleCat.ofHom (threeGeneratorMiddle f g h))
      (ModuleCat.ofHom (threeGeneratorFirst f g h))
      (pointCartierYonedaAmbientMiddle_zero f g h)
      (pointCartierYonedaAmbientMiddle_exact f g h hf hg)
      (pointCartierYonedaUnitTwoCocycle f g h p v b c heq))

/-- The actual principal Cartier extension sends the displayed degree-two
point class to the ambient Koszul class with the explicit unit coefficient. -/
theorem pointCartierYonedaUnitTwoClass_boundary
    (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c)
    (hp : p ∈ R⁰) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) :
    (pointCartierYonedaUnitTwoClass f g h p v b c heq hf hg hh).comp
        (pointCartierYonedaCoefficientComplex_shortExact p hp).extClass
        (show 2 + 1 = 3 by rfl) =
      pointCartierYonedaAmbientClass f g h hf hg hh (v⁻¹ : Rˣ) := by
  let T := pointCartierYonedaAmbientResolution f g h hf hg hh
  let S := pointCartierYonedaCoefficientComplex p
  let φ : T.K₁ ⟶ S.X₃ :=
    degreeTwoCocycleDesc (ModuleCat.ofHom (threeGeneratorMiddle f g h))
      (ModuleCat.ofHom (threeGeneratorFirst f g h))
      (pointCartierYonedaAmbientMiddle_zero f g h)
      (pointCartierYonedaAmbientMiddle_exact f g h hf hg)
      (pointCartierYonedaUnitTwoCocycle f g h p v b c heq)
  let ψ : T.K₂ ⟶ S.X₁ :=
    degreeThreeCocycleDesc (ModuleCat.ofHom (threeGeneratorFirst f g h))
      (0 : ModuleCat.of R PUnit ⟶ ModuleCat.of R R) (by simp)
      (pointCartierYonedaAmbientFirst_exact f g h hf)
      (pointCartierYonedaAmbientTopCocycle (v⁻¹ : Rˣ))
  let l : T.C₂ ⟶ S.X₂ := ModuleCat.ofHom (pointCartierYonedaUnitLift v b c)
  have hleft : T.i₂ ≫ l = ψ ≫ S.f := by
    apply (cancel_epi (Abelian.coimage.π (ModuleCat.ofHom (threeGeneratorFirst f g h)))).1
    change Abelian.coimage.π (ModuleCat.ofHom (threeGeneratorFirst f g h)) ≫
      (Abelian.factorThruCoimage (ModuleCat.ofHom (threeGeneratorFirst f g h)) ≫ l) =
        Abelian.coimage.π (ModuleCat.ofHom (threeGeneratorFirst f g h)) ≫ (ψ ≫ S.f)
    rw [← Category.assoc, Abelian.coimage.fac, ← Category.assoc,
      coimage_π_comp_degreeThreeCocycleDesc]
    apply ModuleCat.hom_ext
    change (pointCartierYonedaUnitLift v b c).comp (threeGeneratorFirst f g h) =
      (LinearMap.lsmul R R p).comp (LinearMap.lsmul R R (v⁻¹ : Rˣ))
    rw [pointCartierYonedaUnitLift_comp_first, ← heq]
    apply LinearMap.ext
    intro x
    change (p * (v⁻¹ : Rˣ)) * x = p * ((v⁻¹ : Rˣ) * x)
    ring
  have hright : T.p₂ ≫ φ = l ≫ S.g := by
    change Abelian.coimage.π (ModuleCat.ofHom (threeGeneratorMiddle f g h)) ≫
      degreeTwoCocycleDesc _ _ _ _ _ = l ≫ S.g
    rw [coimage_π_comp_degreeTwoCocycleDesc]
    rfl
  exact T.prefix_connecting_comp_coefficient_extension S
    (pointCartierYonedaCoefficientComplex_shortExact p hp) φ l ψ hleft hright

end PfaffianDescent

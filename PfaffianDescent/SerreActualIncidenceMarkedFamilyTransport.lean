import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIncidenceMarkedOpen
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen

/-! Derived equality of marked families transports the actual incidence seed
and both old geometric opens, including its parameter/configuration maps. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {S B X P Z T : Scheme.{u}}
variable (cfg : B ⟶ S) (x : X ⟶ S) (pp : P ⟶ S)
variable (zero : Z ⟶ pullback x pp) [IsClosedImmersion zero]
variable (marked₁ marked₂ : Fin 3 → (B ⟶ X))
variable (hm₁ : ∀ i, marked₁ i ≫ x = cfg) (hm₂ : ∀ i, marked₂ i ≫ x = cfg)
variable (hmarked : marked₁ = marked₂)

def serreActualIncidenceMarkedFamilyIso :
    serreThreePointSectionIncidence cfg x pp marked₁ hm₁ zero ≅
      serreThreePointSectionIncidence cfg x pp marked₂ hm₂ zero := by
  subst marked₂
  exact Iso.refl _

@[reassoc]
theorem serreActualIncidenceMarkedFamilyIso_toConfiguration :
    (serreActualIncidenceMarkedFamilyIso cfg x pp zero marked₁ marked₂ hm₁ hm₂ hmarked).hom ≫
      serreThreePointSectionIncidenceToConfiguration cfg x pp marked₂ hm₂ zero =
    serreThreePointSectionIncidenceToConfiguration cfg x pp marked₁ hm₁ zero := by
  subst marked₂
  simp only [serreActualIncidenceMarkedFamilyIso, Iso.refl_hom, Category.id_comp]

@[reassoc]
theorem serreActualIncidenceMarkedFamilyIso_toParameters :
    (serreActualIncidenceMarkedFamilyIso cfg x pp zero marked₁ marked₂ hm₁ hm₂ hmarked).hom ≫
      serreThreePointSectionIncidenceToParameters cfg x pp marked₂ hm₂ zero =
    serreThreePointSectionIncidenceToParameters cfg x pp marked₁ hm₁ zero := by
  subst marked₂
  simp only [serreActualIncidenceMarkedFamilyIso, Iso.refl_hom, Category.id_comp]

theorem serreActualIncidenceMarkedFamilyIso_goodMarked
    [IsProper (zero ≫ pullback.snd x pp)]
    (s : T ⟶ serreThreePointSectionIncidence cfg x pp marked₁ hm₁ zero) (t : T)
    (hgood : s t ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen
      (serreThreePointSectionIncidenceZeroFamily cfg x pp marked₁ hm₁ zero))
    (hsimple : s t ∈ cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen
      cfg x pp marked₁ hm₁ zero) :
    (s ≫ (serreActualIncidenceMarkedFamilyIso cfg x pp zero
      marked₁ marked₂ hm₁ hm₂ hmarked).hom) t ∈
      cubicClosedPointSerreFiniteZeroResidual_goodOpen
        (serreThreePointSectionIncidenceZeroFamily cfg x pp marked₂ hm₂ zero) ∧
    (s ≫ (serreActualIncidenceMarkedFamilyIso cfg x pp zero
      marked₁ marked₂ hm₁ hm₂ hmarked).hom) t ∈
      cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg x pp marked₂ hm₂ zero := by
  subst marked₂
  simpa only [serreActualIncidenceMarkedFamilyIso, Iso.refl_hom, Category.comp_id]
    using And.intro hgood hsimple

end PfaffianDescent

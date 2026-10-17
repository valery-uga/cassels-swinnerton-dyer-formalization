import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedSectionOpen
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceMarkedMaps

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
variable {S B X P Z : Scheme.{u}}
variable (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S)
variable (marked : Fin 3 → (B ⟶ X)) (hmarked : ∀ i, marked i ≫ x = b)
variable (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]

def cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen :
    (serreThreePointSectionIncidence b x p marked hmarked zero).Opens :=
  cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen
    (serreThreePointSectionIncidenceZeroFamily b x p marked hmarked zero)
    (serreIncidenceMarkedZeroSection b x p marked hmarked zero)

theorem cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen_isOpenImmersion
    (i : Fin 3) :
    IsOpenImmersion
      ((cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen
        b x p marked hmarked zero).ι ≫
          serreIncidenceMarkedZeroSection b x p marked hmarked zero i) :=
  cubicClosedPointSerreFiniteZeroResidual_threeMarkedSectionOpen_isOpenImmersion
    (serreThreePointSectionIncidenceZeroFamily b x p marked hmarked zero)
    (serreIncidenceMarkedZeroSection b x p marked hmarked zero)
    (serreIncidenceMarkedZeroSection_toIncidence b x p marked hmarked zero) i

end PfaffianDescent

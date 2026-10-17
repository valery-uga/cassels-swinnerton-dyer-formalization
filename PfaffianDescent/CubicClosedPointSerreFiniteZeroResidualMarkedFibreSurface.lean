import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedFibreStalk
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceMarkedMaps

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem cubicClosedPointSerreFiniteZeroResidual_markedFibreSection_surface
    {S B X P Z T : Scheme.{u}}
    (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S)
    (marked : Fin 3 → (B ⟶ X)) (hm : ∀ n, marked n ≫ x = b)
    (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
    (s : T ⟶ serreThreePointSectionIncidence b x p marked hm zero) (n : Fin 3) :
    cubicClosedPointSerreFiniteZeroResidual_markedFibreSection
      (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero)
      (serreIncidenceMarkedZeroSection b x p marked hm zero n)
      (serreIncidenceMarkedZeroSection_toIncidence b x p marked hm zero n) s ≫
      pullback.fst (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero) s ≫
      pullback.fst (zero ≫ pullback.snd x p)
        (serreThreePointSectionIncidenceToParameters b x p marked hm zero) ≫
      zero ≫ pullback.fst x p =
      s ≫ serreThreePointSectionIncidenceToConfiguration b x p marked hm zero ≫ marked n := by
  simp only [cubicClosedPointSerreFiniteZeroResidual_markedFibreSection,
    serreIncidenceMarkedZeroSection, pullback.lift_fst_assoc, Category.assoc,
    serreIncidenceMarkedToUniversalZero_comp_assoc, fixedLinearSystemIncidenceMap_fst]

end PfaffianDescent

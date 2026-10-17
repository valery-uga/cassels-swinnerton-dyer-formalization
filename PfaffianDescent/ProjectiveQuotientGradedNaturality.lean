import PfaffianDescent.ProjectiveChartQuotientCoefficientNaturality
import AllCharacteristics.ProjectiveCoefficientComposition

/-!
# Naturality of homogeneous quotient maps under coefficient change

The two orders of changing coefficients and passing to a homogeneous
quotient agree already on coordinate rings, and hence as graded maps.
This supplies the algebraic identity used by `Proj.map_comp`.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateQuotientMap_coefficientChanged_comm
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) :
    (coordinateQuotientMap (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_mono f I J hIJ)).comp
        (coordinateCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
          (coefficientChangedHomogeneousIdeal_toIdeal f I)) =
    (coordinateCoefficientMap f J (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_toIdeal f J)).comp
        (coordinateQuotientMap I J hIJ) := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply, coordinateQuotientMap_mk,
    coordinateCoefficientMap_mk]

theorem gradedQuotientMap_coefficientChanged_comm
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) :
    (gradedQuotientMap (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_mono f I J hIJ)).comp
        (gradedCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
          (coefficientChangedHomogeneousIdeal_toIdeal f I)) =
    (gradedCoefficientMap f J (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_toIdeal f J)).comp
        (gradedQuotientMap I J hIJ) := by
  apply GradedRingHom.ext
  intro x
  exact DFunLike.congr_fun
    (coordinateQuotientMap_coefficientChanged_comm f I J hIJ) x

end PfaffianDescent

import PfaffianDescent.HomogeneousQuotientMap
import PfaffianDescent.ProjectiveCoefficientIdealMap
import AllCharacteristics.ProjectiveChartBaseChange

/-!
# Compatibility of projective quotient charts with coefficient change

The chart square formed by a homogeneous quotient and an arbitrary
coefficient change commutes on the actual normalized coordinate charts.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coefficient change and passage to a homogeneous quotient commute on
every standard affine chart. -/
theorem chartQuotientMap_chartCoefficientMap_comm
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (I' J' : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (hI : I.toIdeal.map (MvPolynomial.map f) = I'.toIdeal)
    (hJ : J.toIdeal.map (MvPolynomial.map f) = J'.toIdeal)
    (hI'J' : I'.toIdeal ≤ J'.toIdeal) (j : Fin 4) :
    (chartQuotientMap I' J' hI'J' j).comp
      (chartCoefficientMap f I I' hI j) =
    (chartCoefficientMap f J J' hJ j).comp
      (chartQuotientMap I J hIJ j) := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := eval₂_chartCoordinate_surjective I j x
  change chartQuotientMap I' J' hI'J' j
      (chartCoefficientMap f I I' hI j
        (p.eval₂ (chartBaseMap I j) (chartCoordinate I j))) =
    chartCoefficientMap f J J' hJ j
      (chartQuotientMap I J hIJ j
        (p.eval₂ (chartBaseMap I j) (chartCoordinate I j)))
  simp only [RingHom.comp_apply, chartCoefficientMap_eval,
    chartQuotientMap_eval₂]

/-- Inclusion of homogeneous ideals is preserved by canonical coefficient
change. -/
theorem coefficientChangedHomogeneousIdeal_mono
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) :
    (coefficientChangedHomogeneousIdeal f I).toIdeal ≤
      (coefficientChangedHomogeneousIdeal f J).toIdeal := by
  rw [← coefficientChangedHomogeneousIdeal_toIdeal f I,
    ← coefficientChangedHomogeneousIdeal_toIdeal f J]
  exact Ideal.map_mono hIJ

/-- Canonical coefficient changes commute with the quotient maps on the
actual affine projective charts. -/
theorem chartQuotientMap_coefficientChanged_comm
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4) :
    (chartQuotientMap (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j).comp
      (chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal_toIdeal f I) j) =
    (chartCoefficientMap f J (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_toIdeal f J) j).comp
      (chartQuotientMap I J hIJ j) := by
  exact chartQuotientMap_chartCoefficientMap_comm f I J
    (coefficientChangedHomogeneousIdeal f I)
    (coefficientChangedHomogeneousIdeal f J)
    hIJ (coefficientChangedHomogeneousIdeal_toIdeal f I)
    (coefficientChangedHomogeneousIdeal_toIdeal f J)
    (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j

end PfaffianDescent

import PfaffianDescent.ProjectiveQuotientCoefficientNaturality
import PfaffianDescent.VoisinHomogeneousIdealGenericSpreading
import AllCharacteristics.ProjectiveBaseChange

/-!
# Base change of projective homogeneous quotient immersions

The coefficient-changed quotient immersion is the actual pullback of the
original immersion. This follows from the global naturality square and the
base-change theorem for each projective quotient over its coefficient ring.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The global quotient-immersion square is Cartesian for any chosen
homogeneous ideals whose underlying polynomial ideals are obtained by
coefficient extension. This includes spread-out models of a fixed curve. -/
theorem isPullback_schemeQuotientMap_coefficient_naturality
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (I' J' : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hIJ : I.toIdeal ≤ J.toIdeal) (hI'J' : I'.toIdeal ≤ J'.toIdeal)
    (hI : I.toIdeal.map (MvPolynomial.map f) = I'.toIdeal)
    (hJ : J.toIdeal.map (MvPolynomial.map f) = J'.toIdeal) :
    IsPullback (projectiveCoefficientMap f J J' hJ)
      (schemeQuotientMap I' J' hI'J')
      (schemeQuotientMap I J hIJ)
      (projectiveCoefficientMap f I I' hI) := by
  let b := Spec.map (CommRingCat.ofHom f)
  have hJbase : IsPullback
      (projectiveCoefficientMap f J J' hJ) (toBase J') (toBase J) b :=
    isPullback_projectiveCoefficientMap f J J' hJ
  have hIbase : IsPullback
      (projectiveCoefficientMap f I I' hI) (toBase I') (toBase I) b :=
    isPullback_projectiveCoefficientMap f I I' hI
  have hJbig : IsPullback
      (projectiveCoefficientMap f J J' hJ)
      (schemeQuotientMap I' J' hI'J' ≫ toBase I')
      (schemeQuotientMap I J hIJ ≫ toBase I) b := by
    simpa only [schemeQuotientMap_toBase] using hJbase
  have hc := schemeQuotientMap_coefficient_naturality f
    I J I' J' hIJ hI'J' hI hJ
  exact hJbig.of_bot hc hIbase

/-- The fixed-curve model embedded in a cubic family commutes with
coefficient change as an actual Cartesian square. -/
theorem isPullback_homogeneousModelToCubic_baseChange
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hpJ : p ∈ J.toIdeal)
    (hpC : MvPolynomial.map f p ∈ C.toIdeal)
    (hJC : J.toIdeal.map (MvPolynomial.map f) = C.toIdeal) :
    IsPullback (projectiveCoefficientMap f J C hJC)
      (homogeneousModelToCubic (MvPolynomial.map f p) (hp.map f) C hpC)
      (homogeneousModelToCubic p hp J hpJ)
      (projectiveCoefficientMap f (equationIdeal p hp)
        (equationIdeal (MvPolynomial.map f p) (hp.map f))
        (equationIdeal_map f p hp)) := by
  exact isPullback_schemeQuotientMap_coefficient_naturality f
    (equationIdeal p hp) J
    (equationIdeal (MvPolynomial.map f p) (hp.map f)) C
    (by
      apply Ideal.span_le.mpr
      rintro x rfl
      exact hpJ)
    (by
      apply Ideal.span_le.mpr
      rintro x rfl
      exact hpC)
    (equationIdeal_map f p hp) hJC

theorem isPullback_schemeQuotientMap_coefficientChanged
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) :
    IsPullback
      (projectiveCoefficientMap f J (coefficientChangedHomogeneousIdeal f J)
        (coefficientChangedHomogeneousIdeal_toIdeal f J))
      (schemeQuotientMap (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal f J)
        (coefficientChangedHomogeneousIdeal_mono f I J hIJ))
      (schemeQuotientMap I J hIJ)
      (projectiveCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal_toIdeal f I)) := by
  let I' := coefficientChangedHomogeneousIdeal f I
  let J' := coefficientChangedHomogeneousIdeal f J
  let hI'J' := coefficientChangedHomogeneousIdeal_mono f I J hIJ
  let cI := projectiveCoefficientMap f I I' (coefficientChangedHomogeneousIdeal_toIdeal f I)
  let cJ := projectiveCoefficientMap f J J' (coefficientChangedHomogeneousIdeal_toIdeal f J)
  let q := schemeQuotientMap I J hIJ
  let q' := schemeQuotientMap I' J' hI'J'
  let b := Spec.map (CommRingCat.ofHom f)
  have hJ : IsPullback cJ (toBase J') (toBase J) b :=
    isPullback_projectiveCoefficientMap f J J'
      (coefficientChangedHomogeneousIdeal_toIdeal f J)
  have hI : IsPullback cI (toBase I') (toBase I) b :=
    isPullback_projectiveCoefficientMap f I I'
      (coefficientChangedHomogeneousIdeal_toIdeal f I)
  have hJ' : IsPullback cJ (q' ≫ toBase I') (q ≫ toBase I) b := by
    simpa only [q, q', schemeQuotientMap_toBase] using hJ
  have hc : cJ ≫ q = q' ≫ cI := by
    exact (schemeQuotientMap_coefficientChanged_comm f I J hIJ).symm
  exact hJ'.of_bot hc hI

end PfaffianDescent

import PfaffianDescent.RegularPrincipalAffineIdealSheafBaseChange
import PfaffianDescent.ProjectiveChartQuotientCoefficientNaturality
import PfaffianDescent.ProjectiveChartRelativeRegularBaseChange

/-!
# Canonical ideal base change on projective quotient charts

This applies the nonflat regular-principal affine theorem to the
actual chart maps of a homogeneous projective quotient.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical ideal-sheaf map on a projective quotient chart is an
isomorphism after arbitrary coefficient change if the original chart
ideal is regular principal and its generator stays regular on the
actual coefficient-changed chart. -/
theorem isIso_chartQuotientMap_idealBaseChange_of_regular
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (x : ChartRing I j) (hx : IsRegular x)
    (hker : RingHom.ker (chartQuotientMap I J hIJ j) =
      Ideal.span ({x} : Set (ChartRing I j)))
    (hchanged : IsRegular
      (chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal_toIdeal f I) j x)) :
    let g := chartCoefficientMap f I
      (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal_toIdeal f I) j
    let q := chartQuotientMap I J hIJ j
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
      IsClosedImmersion.spec_of_surjective _
        (chartQuotientMap_surjective I J hIJ j)
    IsIso (closedImmersionIdealBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom q))) := by
  let g := chartCoefficientMap f I
    (coefficientChangedHomogeneousIdeal f I)
    (coefficientChangedHomogeneousIdeal_toIdeal f I) j
  let q := chartQuotientMap I J hIJ j
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
    IsClosedImmersion.spec_of_surjective _
      (chartQuotientMap_surjective I J hIJ j)
  exact isIso_regularPrincipalSurjectiveAffineIdealBaseChangeHom
    g q (chartQuotientMap_surjective I J hIJ j)
    x hx hchanged hker

/-- A relatively flat regular-principal projective quotient chart has
the canonical ideal-sheaf base-change isomorphism for every coefficient
map. No flatness is required of that coefficient map. -/
theorem isIso_chartQuotientMap_idealBaseChange_of_flat_regular
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (x : ChartRing I j) (hx : IsRegular x)
    (hker : RingHom.ker (chartQuotientMap I J hIJ j) =
      Ideal.span ({x} : Set (ChartRing I j)))
    (hflat : ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat) :
    let g := chartCoefficientMap f I
      (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal_toIdeal f I) j
    let q := chartQuotientMap I J hIJ j
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
      IsClosedImmersion.spec_of_surjective _
        (chartQuotientMap_surjective I J hIJ j)
    IsIso (closedImmersionIdealBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom q))) := by
  exact isIso_chartQuotientMap_idealBaseChange_of_regular
    f I J hIJ j x hx hker
      (chartCoefficientMap_regular_of_flat_quotientChart
        f I J hIJ j x hx hker hflat)

/-- Every chart of a regular-principal projective quotient with
relatively flat quotient charts has the canonical ideal-sheaf
base-change isomorphism after any coefficient change. -/
theorem HasRegularPrincipalStandardCharts.isIso_idealBaseChange_onChart
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (H : HasRegularPrincipalStandardCharts I J hIJ)
    (hflat : ∀ j : Fin 4,
      ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat)
    (j : Fin 4) :
    let g := chartCoefficientMap f I
      (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal_toIdeal f I) j
    let q := chartQuotientMap I J hIJ j
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
      IsClosedImmersion.spec_of_surjective _
        (chartQuotientMap_surjective I J hIJ j)
    IsIso (closedImmersionIdealBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom q))) := by
  obtain ⟨x, hx, hker⟩ := H j
  exact isIso_chartQuotientMap_idealBaseChange_of_flat_regular
    f I J hIJ j x hx hker (hflat j)

end PfaffianDescent

import PfaffianDescent.ProjectiveQuotientIdealPullbackChart
import PfaffianDescent.ProjectiveChartRegularPrincipalIdealBaseChange

/-!
# Global ideal-module base change for regular-principal projective quotients

The canonical ideal-module map of a closed projective quotient immersion
is an isomorphism after arbitrary coefficient change when every original
standard chart has a regular principal quotient ideal and its quotient
chart is flat over the coefficient ring.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem HasRegularPrincipalStandardCharts.isIso_globalIdealBaseChange
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (H : HasRegularPrincipalStandardCharts I J hIJ)
    (hflat : ∀ j : Fin 4,
      ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat) :
    let cI := projectiveCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal_toIdeal f I)
    let q := schemeQuotientMap I J hIJ
    letI : IsClosedImmersion q := schemeQuotientMap_closedImmersion I J hIJ
    IsIso (closedImmersionIdealBaseChangeHom cI q) := by
  let I' := coefficientChangedHomogeneousIdeal f I
  let cI := projectiveCoefficientMap f I I'
    (coefficientChangedHomogeneousIdeal_toIdeal f I)
  let q := schemeQuotientMap I J hIJ
  letI : IsClosedImmersion q := schemeQuotientMap_closedImmersion I J hIJ
  apply isIso_closedImmersionIdealBaseChangeHom_of_openCover_comp_mono
    cI q (coordinateOpenCover I').openCover
  intro j
  change Fin 4 at j
  change Mono ((Scheme.Modules.pullback ((chartι I' j) ≫ cI)).map
    (IdealSheafDataModule.closedImmersionModuleToUnit q))
  let g := Spec.map (CommRingCat.ofHom
    (chartCoefficientMap f I I' (coefficientChangedHomogeneousIdeal_toIdeal f I) j))
  let qj := Spec.map (CommRingCat.ofHom (chartQuotientMap I J hIJ j))
  letI : IsClosedImmersion qj := IsClosedImmersion.spec_of_surjective _
    (chartQuotientMap_surjective I J hIJ j)
  have hIso : IsIso (closedImmersionIdealBaseChangeHom g qj) :=
    H.isIso_idealBaseChange_onChart f I J hIJ hflat j
  letI : IsIso (closedImmersionIdealBaseChangeHom g qj) := hIso
  have hlocal := closedImmersionIdealPullback_mono_of_baseChangeIso g qj
  exact chartQuotientMap_globalIdealPullback_mono f I J hIJ j hlocal

end PfaffianDescent

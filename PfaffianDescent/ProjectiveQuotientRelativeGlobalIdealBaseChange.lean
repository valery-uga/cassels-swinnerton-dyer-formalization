import PfaffianDescent.ProjectiveChartRelativeIdealSheafMono
import PfaffianDescent.ProjectiveQuotientIdealPullbackChart
import PfaffianDescent.ProjectiveQuotientFlatCharts

/-!
# Global ideal base change from relative quotient flatness

If each quotient chart is flat over the parameter ring, the canonical ideal
base-change map for the projective quotient is an isomorphism after an
arbitrary coefficient change. No regular-principal presentation is needed.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIso_projectiveQuotient_globalIdealBaseChange_of_flatQuotientCharts
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal)
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
  exact chartQuotientMap_globalIdealPullback_mono f I J hIJ j
    (chartQuotientMap_actualIdealPullback_mono_of_flat
      f I J hIJ j (hflat j))

/-- Relative flatness of the projective quotient itself suffices for
arbitrary coefficient change of its canonical global ideal sheaf. -/
theorem isIso_projectiveQuotient_globalIdealBaseChange_of_flatToBase
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (hflat : Flat (toBase J)) :
    let cI := projectiveCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal_toIdeal f I)
    let q := schemeQuotientMap I J hIJ
    letI : IsClosedImmersion q := schemeQuotientMap_closedImmersion I J hIJ
    IsIso (closedImmersionIdealBaseChangeHom cI q) := by
  exact isIso_projectiveQuotient_globalIdealBaseChange_of_flatQuotientCharts
    f I J hIJ (flat_quotientCharts_of_flat_toBase I J hIJ hflat)

end PfaffianDescent

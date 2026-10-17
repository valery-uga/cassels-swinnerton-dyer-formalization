import PfaffianDescent.ProjectiveChartAlgebraPushout
import PfaffianDescent.ProjectiveChartKernelTensorExact
import PfaffianDescent.RelativeAffineIdealPullbackMono
import PfaffianDescent.RegularPrincipalAffineIdealSheafBaseChange

/-!
# Relative ideal-sheaf pullback on actual projective charts

The quotient-chart ideal of a relatively flat projective family remains
embedded in the structure sheaf after arbitrary coefficient change.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem chartQuotientMap_idealPullback_mono_of_flat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (hflat : ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat) :
    let C := coefficientChangedHomogeneousIdeal f I
    let hIC := coefficientChangedHomogeneousIdeal_toIdeal f I
    let g := chartCoefficientMap f I C hIC j
    let Q := RingHom.ker (chartQuotientMap I J hIJ j)
    Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q))))) := by
  let C := coefficientChangedHomogeneousIdeal f I
  let hIC := coefficientChangedHomogeneousIdeal_toIdeal f I
  let g := chartCoefficientMap f I C hIC j
  let Q := RingHom.ker (chartQuotientMap I J hIJ j)
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul R (ChartRing J j) := Algebra.toSMul
  letI : Module R (ChartRing J j) := Algebra.toModule
  letI : Algebra S (ChartRing C j) := (chartBaseMap C j).toAlgebra
  letI : SMul S (ChartRing C j) := Algebra.toSMul
  letI : Module S (ChartRing C j) := Algebra.toModule
  letI : Algebra R (ChartRing C j) := (g.comp (chartBaseMap I j)).toAlgebra
  letI : SMul R (ChartRing C j) := Algebra.toSMul
  letI : Module R (ChartRing C j) := Algebra.toModule
  have hTowerS : IsScalarTower R S (ChartRing C j) :=
    .of_algebraMap_eq fun r => by
      change g (chartBaseMap I j r) = chartBaseMap C j (f r)
      exact chartCoefficientMap_baseMap f I C hIC j r
  letI : IsScalarTower R S (ChartRing C j) := hTowerS
  have hTowerA : letI : Algebra (ChartRing I j) (ChartRing C j) := g.toAlgebra
      IsScalarTower R (ChartRing I j) (ChartRing C j) := by
    letI : Algebra (ChartRing I j) (ChartRing C j) := g.toAlgebra
    exact .of_algebraMap_eq fun _ => rfl
  have hPushout : letI : Algebra (ChartRing I j) (ChartRing C j) := g.toAlgebra
      Algebra.IsPushout R S (ChartRing I j) (ChartRing C j) :=
    chartCoefficientMap_isPushout_algebra f I j
  haveI : Module.Flat R (ChartRing J j) := by
    rw [chartQuotientMap_chartBaseMap I J hIJ j] at hflat
    exact hflat
  haveI : Module.Flat R ((ChartRing I j) ⧸ Q) :=
    relativeSurjectiveAlgebraHom_quotientKer_flat
      (chartQuotientAlgHom I J hIJ j)
      (chartQuotientMap_surjective I J hIJ j)
  exact affineQuotientIdealModulePullback_mono_of_quotient_flat_pushout
    g Q hTowerA hPushout

/-- The preceding result for the actual surjective quotient-chart map,
rather than its quotient-by-kernel presentation. -/
theorem chartQuotientMap_actualIdealPullback_mono_of_flat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (hflat : ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat) :
    let C := coefficientChangedHomogeneousIdeal f I
    let g := chartCoefficientMap f I C
      (coefficientChangedHomogeneousIdeal_toIdeal f I) j
    let q := chartQuotientMap I J hIJ j
    Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom q)))) := by
  let C := coefficientChangedHomogeneousIdeal f I
  let g := chartCoefficientMap f I C
    (coefficientChangedHomogeneousIdeal_toIdeal f I) j
  let q := chartQuotientMap I J hIJ j
  let Q := RingHom.ker q
  have hm := chartQuotientMap_idealPullback_mono_of_flat f I J hIJ j hflat
  have hker : (Spec.map (CommRingCat.ofHom q)).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q))).ker :=
    specMap_ker_eq_quotient_of_ker_eq q Q rfl
  change Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
    (IdealSheafDataModule.idealModuleToUnit
      (Spec.map (CommRingCat.ofHom q)).ker))
  rw [hker]
  exact hm

end PfaffianDescent

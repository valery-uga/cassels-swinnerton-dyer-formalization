import PfaffianDescent.ProjectiveChartTensorBaseChange
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Algebraic pushout structure on actual projective charts

The categorical coefficient-change square for an actual standard chart
supplies the algebraic pushout structure used by relative ideal exactness.
-/

namespace PfaffianDescent

open CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem chartCoefficientMap_isPushout_algebra
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (j : Fin 4) :
    let C := coefficientChangedHomogeneousIdeal f J
    let hJC := coefficientChangedHomogeneousIdeal_toIdeal f J
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
    letI : SMul R (ChartRing J j) := Algebra.toSMul
    letI : Module R (ChartRing J j) := Algebra.toModule
    letI : Algebra S (ChartRing C j) := (chartBaseMap C j).toAlgebra
    letI : SMul S (ChartRing C j) := Algebra.toSMul
    letI : Module S (ChartRing C j) := Algebra.toModule
    letI : Algebra (ChartRing J j) (ChartRing C j) :=
      (chartCoefficientMap f J C hJC j).toAlgebra
    letI : Algebra R (ChartRing C j) :=
      ((chartCoefficientMap f J C hJC j).comp (chartBaseMap J j)).toAlgebra
    letI : SMul R (ChartRing C j) := Algebra.toSMul
    letI : Module R (ChartRing C j) := Algebra.toModule
    letI : IsScalarTower R (ChartRing J j) (ChartRing C j) :=
      .of_algebraMap_eq (fun _ => rfl)
    letI : IsScalarTower R S (ChartRing C j) :=
      .of_algebraMap_eq (fun r => chartCoefficientMap_baseMap f J C hJC j r)
    Algebra.IsPushout R S (ChartRing J j) (ChartRing C j) := by
  let C := coefficientChangedHomogeneousIdeal f J
  let hJC := coefficientChangedHomogeneousIdeal_toIdeal f J
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul R (ChartRing J j) := Algebra.toSMul
  letI : Module R (ChartRing J j) := Algebra.toModule
  letI : Algebra S (ChartRing C j) := (chartBaseMap C j).toAlgebra
  letI : SMul S (ChartRing C j) := Algebra.toSMul
  letI : Module S (ChartRing C j) := Algebra.toModule
  letI : Algebra (ChartRing J j) (ChartRing C j) :=
    (chartCoefficientMap f J C hJC j).toAlgebra
  letI : Algebra R (ChartRing C j) :=
    ((chartCoefficientMap f J C hJC j).comp (chartBaseMap J j)).toAlgebra
  letI : SMul R (ChartRing C j) := Algebra.toSMul
  letI : Module R (ChartRing C j) := Algebra.toModule
  haveI : IsScalarTower R (ChartRing J j) (ChartRing C j) :=
    .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R S (ChartRing C j) :=
    .of_algebraMap_eq fun r => by
      change chartCoefficientMap f J C hJC j (chartBaseMap J j r) =
        chartBaseMap C j (f r)
      exact chartCoefficientMap_baseMap f J C hJC j r
  have h := (isPushout_chartCoefficientMap f J C hJC j).flip
  exact (CommRingCat.isPushout_iff_isPushout).mp h

end PfaffianDescent

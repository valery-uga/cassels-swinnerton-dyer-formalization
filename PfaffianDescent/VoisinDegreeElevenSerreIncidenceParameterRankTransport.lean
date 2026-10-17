import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNineParameterIso
import AllCharacteristics.CoordinateCharts

/-! # Literal projective bases and normalized charts under actual rank equality -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceParameterRankIso
    (K : Type u) [CommRing K] {n m : ℕ} (h : n = m) :
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) ≅
      scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) :=
  eqToIso (congrArg (fun k =>
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin k) K))) h)

@[reassoc]
theorem serreIncidenceParameterRankIso_toBase
    (K : Type u) [CommRing K] {n m : ℕ} (h : n = m) :
    (serreIncidenceParameterRankIso K h).hom ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) =
    toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) := by
  subst m
  simp [serreIncidenceParameterRankIso]

def serreIncidenceParameterRankChartEquiv
    (K : Type u) [CommRing K] {n m : ℕ} (h : n = m) (j : Fin n) :
    ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j ≃+*
      ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) ((finCongr h) j) := by
  subst m
  exact RingEquiv.refl _

theorem serreIncidenceParameterRankChart_coordinate
    (K : Type u) [CommRing K] {n m : ℕ} (h : n = m) (j k : Fin n) :
    serreIncidenceParameterRankChartEquiv K h j
      (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j k) =
    chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))
      ((finCongr h) j) ((finCongr h) k) := by
  subst m
  rfl

end PfaffianDescent

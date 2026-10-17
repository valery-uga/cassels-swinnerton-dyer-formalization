import PfaffianDescent.AmbientPointKoszulFlatBaseChange
import PfaffianDescent.AmbientPointKoszulStalkCoordinates
import Mathlib.RingTheory.Flat.Localization

/-! # Exactness of the coordinate Koszul matrices in actual projective stalks

The actual chart-to-stalk homomorphism is a localization. Thus the explicit
Koszul matrices are exact in the homogeneous local ring at every point of
projective three-space. Their parameters are the same local equations as
the actual coordinate-multiplication sheaf stalk maps.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The coordinate Koszul complex is exact at its rank-three degree-two
term on every actual standard affine chart. -/
theorem ambientPointKoszul_chart_exact_middle (j : Fin 4) :
    LinearMap.range (threeGeneratorFirst
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 2)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)) =
    LinearMap.ker (threeGeneratorMiddle
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 2)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)) := by
  by_cases hj : j = 0
  · subst j
    exact ambientPointKoszul_chartZero_exact_middle K
  · exact (ambientPointKoszul_chartNonzero_exact K j hj).2.1

/-- The coordinate Koszul complex is exact at its rank-three degree-one
term on every actual standard affine chart. -/
theorem ambientPointKoszul_chart_exact_last (j : Fin 4) :
    LinearMap.range (threeGeneratorMiddle
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 2)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)) =
    LinearMap.ker (threeGeneratorLast
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 2)
      (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)) := by
  by_cases hj : j = 0
  · subst j
    exact ambientPointKoszul_chartZero_exact_last K
  · exact (ambientPointKoszul_chartNonzero_exact K j hj).2.2.1

namespace ProjectiveNegativeTwist

local instance ambientPointKoszul_stalkPointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

/-- The concrete coefficient in the actual coordinate-multiplication
stalk map, with the chosen chart coordinate as denominator. -/
abbrev ambientPointKoszul_stalkParameter
    (i j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) :
    AtPrime PS (pointIdeal PS x) :=
  localEquation PS (pointIdeal PS x) ⟨X i, isHomogeneous_X K i⟩
    ⟨X j, isHomogeneous_X K j⟩ hx

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at degree two in the actual homogeneous local ring. -/
theorem ambientPointKoszul_stalk_exact_middle
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) :
    LinearMap.range (threeGeneratorFirst
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)) =
    LinearMap.ker (threeGeneratorMiddle
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)) := by
  let R := Away PS (X j)
  let S := AtPrime PS (pointIdeal PS x)
  letI : Algebra R S := (ambientPointKoszul_chartToStalk K j x hx).toAlgebra
  let xj : Proj.basicOpen PS (X j) := ⟨x, hx⟩
  let p := ((ProjectiveSpectrum.Proj.toSpec PS (X j)).base xj).asIdeal.primeCompl
  letI : IsLocalization p S := ambientPointKoszul_chartToStalk_isLocalization K j x hx
  letI : Module.Flat R S := IsLocalization.flat S p
  have hex := ambientPointKoszul_flat_exact_middle R S
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 2)
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)
    (ambientPointKoszul_chart_exact_middle K j)
  change LinearMap.range (threeGeneratorFirst
      (ambientPointKoszul_chartToStalk K j x hx _)
      (ambientPointKoszul_chartToStalk K j x hx _)
      (ambientPointKoszul_chartToStalk K j x hx _)) =
    LinearMap.ker (threeGeneratorMiddle
      (ambientPointKoszul_chartToStalk K j x hx _)
      (ambientPointKoszul_chartToStalk K j x hx _)
      (ambientPointKoszul_chartToStalk K j x hx _)) at hex
  simpa only [ambientPointKoszul_chartToStalk_coordinate] using hex

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at degree one in the actual homogeneous local ring. -/
theorem ambientPointKoszul_stalk_exact_last
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) :
    LinearMap.range (threeGeneratorMiddle
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)) =
    LinearMap.ker (threeGeneratorLast
      (ambientPointKoszul_stalkParameter K 1 j x hx)
      (ambientPointKoszul_stalkParameter K 2 j x hx)
      (ambientPointKoszul_stalkParameter K 3 j x hx)) := by
  let R := Away PS (X j)
  let S := AtPrime PS (pointIdeal PS x)
  letI : Algebra R S := (ambientPointKoszul_chartToStalk K j x hx).toAlgebra
  let xj : Proj.basicOpen PS (X j) := ⟨x, hx⟩
  let p := ((ProjectiveSpectrum.Proj.toSpec PS (X j)).base xj).asIdeal.primeCompl
  letI : IsLocalization p S := ambientPointKoszul_chartToStalk_isLocalization K j x hx
  letI : Module.Flat R S := IsLocalization.flat S p
  have hex := ambientPointKoszul_flat_exact_last R S
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 1)
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 2)
    (ambientChartCoordinate (R := K) (σ := Fin 4) j 3)
    (ambientPointKoszul_chart_exact_last K j)
  change LinearMap.range (threeGeneratorMiddle
      (ambientPointKoszul_chartToStalk K j x hx _)
      (ambientPointKoszul_chartToStalk K j x hx _)
      (ambientPointKoszul_chartToStalk K j x hx _)) =
    LinearMap.ker (threeGeneratorLast
      (ambientPointKoszul_chartToStalk K j x hx _)
      (ambientPointKoszul_chartToStalk K j x hx _)
      (ambientPointKoszul_chartToStalk K j x hx _)) at hex
  simpa only [ambientPointKoszul_chartToStalk_coordinate] using hex

end ProjectiveNegativeTwist
end PfaffianDescent

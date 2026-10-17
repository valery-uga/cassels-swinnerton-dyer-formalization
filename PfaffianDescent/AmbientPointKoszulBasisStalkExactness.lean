import PfaffianDescent.AmbientPointKoszulBasisGeometry

/-! # Exactness of the actual basis Koszul parameters in native projective stalks -/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

local instance basisStalkPointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

abbrev ambientPointKoszul_basisStalkParameter
    (M : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) (x : Proj PS)
    (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl) :
    AtPrime PS (pointIdeal PS x) :=
  localEquation PS (pointIdeal PS x) (ambientPointKoszul_basis M i)
    (ambientPointKoszul_basis M j) hx

def ambientPointKoszul_basisChartToStalk
    (M : Matrix (Fin 4) (Fin 4) K) (j : Fin 4) (x : Proj PS)
    (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl) :
    Away PS (ambientPointKoszul_basis M j).val →+* AtPrime PS (pointIdeal PS x) :=
  HomogeneousLocalization.mapId PS (Submonoid.powers_le.mpr hx)

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointKoszul_basisChartToStalk_coordinate
    (M : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) (x : Proj PS)
    (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl) :
    ambientPointKoszul_basisChartToStalk M j x hx
      (ambientPointKoszul_basisChartCoordinate M j i) =
    ambientPointKoszul_basisStalkParameter M i j x hx := by
  apply HomogeneousLocalization.val_injective
  simp only [ambientPointKoszul_basisChartToStalk, HomogeneousLocalization.mapId,
    ambientPointKoszul_basisChartCoordinate, AllCharacteristics.GradedChart.normalized, Away.mk,
    HomogeneousLocalization.map_mk, ambientPointKoszul_basisStalkParameter,
    localEquation, degreeOnePower, pow_one, HomogeneousLocalization.val_mk, GradedRingHom.id_apply]

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointKoszul_basisChartToStalk_isLocalization
    (M : Matrix (Fin 4) (Fin 4) K) (j : Fin 4) (x : Proj PS)
    (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl) :
    let xj : Proj.basicOpen PS (ambientPointKoszul_basis M j).val := ⟨x, hx⟩
    @IsLocalization (Away PS (ambientPointKoszul_basis M j).val) _
      ((ProjectiveSpectrum.Proj.toSpec PS (ambientPointKoszul_basis M j).val).base xj).asIdeal.primeCompl
      (AtPrime PS (pointIdeal PS x)) _ (ambientPointKoszul_basisChartToStalk M j x hx).toAlgebra := by
  dsimp only
  exact ProjectiveSpectrum.Proj.isLocalization_atPrime PS (ambientPointKoszul_basis M j).val
    ⟨x, hx⟩ (ambientPointKoszul_basis M j).property (by decide : 0 < 1)

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointKoszul_basisStalk_exact_middle
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (j : Fin 4) (x : Proj PS)
    (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl) :
    LinearMap.range (threeGeneratorFirst
      (ambientPointKoszul_basisStalkParameter M 1 j x hx)
      (ambientPointKoszul_basisStalkParameter M 2 j x hx)
      (ambientPointKoszul_basisStalkParameter M 3 j x hx)) =
    LinearMap.ker (threeGeneratorMiddle
      (ambientPointKoszul_basisStalkParameter M 1 j x hx)
      (ambientPointKoszul_basisStalkParameter M 2 j x hx)
      (ambientPointKoszul_basisStalkParameter M 3 j x hx)) := by
  let R := Away PS (ambientPointKoszul_basis M j).val
  let S := AtPrime PS (pointIdeal PS x)
  letI : Algebra R S := (ambientPointKoszul_basisChartToStalk M j x hx).toAlgebra
  let xj : Proj.basicOpen PS (ambientPointKoszul_basis M j).val := ⟨x, hx⟩
  let p := ((ProjectiveSpectrum.Proj.toSpec PS (ambientPointKoszul_basis M j).val).base xj).asIdeal.primeCompl
  letI : IsLocalization p S := ambientPointKoszul_basisChartToStalk_isLocalization M j x hx
  letI : Module.Flat R S := IsLocalization.flat S p
  have hex := ambientPointKoszul_flat_exact_middle R S
    (ambientPointKoszul_basisChartCoordinate M j 1)
    (ambientPointKoszul_basisChartCoordinate M j 2)
    (ambientPointKoszul_basisChartCoordinate M j 3)
    (ambientPointKoszul_basisChart_exact_middle M hM j)
  change LinearMap.range (threeGeneratorFirst
      (ambientPointKoszul_basisChartToStalk M j x hx _)
      (ambientPointKoszul_basisChartToStalk M j x hx _)
      (ambientPointKoszul_basisChartToStalk M j x hx _)) =
    LinearMap.ker (threeGeneratorMiddle
      (ambientPointKoszul_basisChartToStalk M j x hx _)
      (ambientPointKoszul_basisChartToStalk M j x hx _)
      (ambientPointKoszul_basisChartToStalk M j x hx _)) at hex
  simpa only [ambientPointKoszul_basisChartToStalk_coordinate] using hex

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointKoszul_basisStalk_exact_last
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (j : Fin 4) (x : Proj PS)
    (hx : (ambientPointKoszul_basis M j).val ∈ (pointIdeal PS x).primeCompl) :
    LinearMap.range (threeGeneratorMiddle
      (ambientPointKoszul_basisStalkParameter M 1 j x hx)
      (ambientPointKoszul_basisStalkParameter M 2 j x hx)
      (ambientPointKoszul_basisStalkParameter M 3 j x hx)) =
    LinearMap.ker (threeGeneratorLast
      (ambientPointKoszul_basisStalkParameter M 1 j x hx)
      (ambientPointKoszul_basisStalkParameter M 2 j x hx)
      (ambientPointKoszul_basisStalkParameter M 3 j x hx)) := by
  let R := Away PS (ambientPointKoszul_basis M j).val
  let S := AtPrime PS (pointIdeal PS x)
  letI : Algebra R S := (ambientPointKoszul_basisChartToStalk M j x hx).toAlgebra
  let xj : Proj.basicOpen PS (ambientPointKoszul_basis M j).val := ⟨x, hx⟩
  let p := ((ProjectiveSpectrum.Proj.toSpec PS (ambientPointKoszul_basis M j).val).base xj).asIdeal.primeCompl
  letI : IsLocalization p S := ambientPointKoszul_basisChartToStalk_isLocalization M j x hx
  letI : Module.Flat R S := IsLocalization.flat S p
  have hex := ambientPointKoszul_flat_exact_last R S
    (ambientPointKoszul_basisChartCoordinate M j 1)
    (ambientPointKoszul_basisChartCoordinate M j 2)
    (ambientPointKoszul_basisChartCoordinate M j 3)
    (ambientPointKoszul_basisChart_exact_last M hM j)
  change LinearMap.range (threeGeneratorMiddle
      (ambientPointKoszul_basisChartToStalk M j x hx _)
      (ambientPointKoszul_basisChartToStalk M j x hx _)
      (ambientPointKoszul_basisChartToStalk M j x hx _)) =
    LinearMap.ker (threeGeneratorLast
      (ambientPointKoszul_basisChartToStalk M j x hx _)
      (ambientPointKoszul_basisChartToStalk M j x hx _)
      (ambientPointKoszul_basisChartToStalk M j x hx _)) at hex
  simpa only [ambientPointKoszul_basisChartToStalk_coordinate] using hex

end PfaffianDescent.ProjectiveNegativeTwist

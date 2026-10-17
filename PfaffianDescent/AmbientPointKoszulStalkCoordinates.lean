import PfaffianDescent.AmbientPointKoszulChartAlgebra

/-! # Actual twist-stalk coordinates for the ambient point Koszul maps

The categorical stalks of the actual negative twists are identified with
the homogeneous local ring in a chosen coordinate chart. The actual
coordinate multiplication map is multiplication by its normalized local
equation under these identifications.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

local instance ambientPointKoszul_pointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

/-- Actual categorical negative-twist stalks in a chosen coordinate chart. -/
def ambientPointKoszul_stalkCoordinate
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) (m : ℕ) :
    (↑((schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS m)) : Type u) ≃+
      AtPrime PS (pointIdeal PS x) := by
  letI : (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x
  exact (stalkAddEquivFractionModule PS m x).trans
    (localTrivialization PS (pointIdeal PS x) ⟨X j, isHomogeneous_X K j⟩ hx m).toAddEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual categorical coordinate-multiplication stalk map becomes
multiplication by `Xi/Xj` in the homogeneous local ring. -/
theorem ambientPointKoszul_stalkCoordinate_mul
    (i j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) (m : ℕ)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS (m + 1))) :
    ambientPointKoszul_stalkCoordinate K j x hx m
        ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3CoordinateMul K i m) z) =
      localEquation PS (pointIdeal PS x) ⟨X i, isHomogeneous_X K i⟩
        ⟨X j, isHomogeneous_X K j⟩ hx *
          ambientPointKoszul_stalkCoordinate K j x hx (m + 1) z := by
  letI : (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x
  let t := localTrivialization PS (pointIdeal PS x) ⟨X j, isHomogeneous_X K j⟩ hx
  change (t m).symm
      (stalkToFractionModule PS m x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (mulHomogeneousPresheaf PS ⟨X i, isHomogeneous_X K i⟩ m) z)) =
    localEquation PS (pointIdeal PS x) ⟨X i, isHomogeneous_X K i⟩
      ⟨X j, isHomogeneous_X K j⟩ hx *
        (t (m + 1)).symm (stalkToFractionModule PS (m + 1) x z)
  rw [stalkToFractionModule_stalkMap]
  rw [← (t (m + 1)).apply_symm_apply (stalkToFractionModule PS (m + 1) x z)]
  rw [mulHomogeneousStalk_localTrivialization_apply]
  dsimp only [t]
  simp only [LinearEquiv.symm_apply_apply]

/-- The actual chart-to-homogeneous-stalk coefficient homomorphism. -/
def ambientPointKoszul_chartToStalk
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) :
    Away PS (X j) →+* AtPrime PS (pointIdeal PS x) :=
  HomogeneousLocalization.mapId PS (Submonoid.powers_le.mpr hx)

set_option backward.isDefEq.respectTransparency false in
/-- Actual normalized ambient chart coordinates have precisely the local
equations appearing in the actual twist-stalk differential. -/
theorem ambientPointKoszul_chartToStalk_coordinate
    (i j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) :
    ambientPointKoszul_chartToStalk K j x hx
      (ambientChartCoordinate (R := K) (σ := Fin 4) j i) =
    localEquation PS (pointIdeal PS x) ⟨X i, isHomogeneous_X K i⟩
      ⟨X j, isHomogeneous_X K j⟩ hx := by
  apply HomogeneousLocalization.val_injective
  simp only [ambientPointKoszul_chartToStalk, HomogeneousLocalization.mapId,
    ambientChartCoordinate, AllCharacteristics.GradedChart.normalized, Away.mk,
    HomogeneousLocalization.map_mk, localEquation, degreeOnePower, pow_one,
    HomogeneousLocalization.val_mk, GradedRingHom.id_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The actual homogeneous point stalk is the localization of its actual
coordinate chart ring at the corresponding affine prime. -/
theorem ambientPointKoszul_chartToStalk_isLocalization
    (j : Fin 4) (x : Proj PS) (hx : X j ∈ (pointIdeal PS x).primeCompl) :
    let xj : Proj.basicOpen PS (X j) := ⟨x, hx⟩
    @IsLocalization (Away PS (X j)) _ ((ProjectiveSpectrum.Proj.toSpec PS (X j)).base xj).asIdeal.primeCompl
      (AtPrime PS (pointIdeal PS x)) _ (ambientPointKoszul_chartToStalk K j x hx).toAlgebra := by
  dsimp only
  exact ProjectiveSpectrum.Proj.isLocalization_atPrime PS (X j) ⟨x, hx⟩
    (isHomogeneous_X K j) (by decide : 0 < 1)

end PfaffianDescent.ProjectiveNegativeTwist

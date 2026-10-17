import PfaffianDescent.ThreeQuadricOThreePairingNaturality

/-! SOURCE ONLY / UNVERIFIED. Native mixed pairing isomorphisms for the
actual O(3)-twisted quadric Koszul terms. Coordinate-power naturality and
actual local invertibility derive all tensor identifications internally. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/- Named arithmetic proofs prevent a redundant `by decide` tactic block
from being visited after expected-type unification already fixes the proof. -/
private theorem p3PairingIso_three_le_four : (3 : ℕ) ≤ 4 := by decide
private theorem p3PairingIso_three_le_six : (3 : ℕ) ≤ 6 := by decide
private theorem p3PairingIso_three_le_three : (3 : ℕ) ≤ 3 := le_rfl
private theorem p3PairingIso_two_le_three : (2 : ℕ) ≤ 3 := by decide

private theorem p3PositiveMulCoordinatePower_isIso
    (j : Fin 4) (d : ℕ) (hd : 0 < d) (m : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι).map
      (positiveMulHomogeneous PS (degreeOnePower PS (p3Coordinate K j) d) m)) := by
  have hU : homogeneousBasicOpen PS
      (degreeOnePower PS (p3Coordinate K j) d : MvPolynomial (Fin 4) K) =
      p3StandardOpen (K := K) j := by
    change ProjectiveSpectrum.basicOpen PS ((X j) ^ d) = ProjectiveSpectrum.basicOpen PS (X j)
    exact ProjectiveSpectrum.basicOpen_pow PS (X j) d hd
  rw [← hU]
  exact restrict_positiveMulHomogeneous_isIso_on_basicOpen PS
    (degreeOnePower PS (p3Coordinate K j) d) m
    (mvPolynomial_irrelevant_le_span_degreeOne_small (K := K) (σ := Fin 4))

private theorem p3Hom_isIso_of_coordinate_restrictions
    {M N : (Proj PS).Modules} (φ : M ⟶ N)
    (h : ∀ j : Fin 4, IsIso ((Scheme.Modules.restrictFunctor
      (p3StandardOpen (K := K) j).ι).map φ)) : IsIso φ := by
  let U := p3StandardOpenLifted (K := K)
  let F : ∀ j : P3CoordinateIndex, (Proj PS).Modules ⥤
      SheafOfModules ((Proj PS).ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor (Proj PS).ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U (p3StandardOpenLifted_coversTop K)
  letI : ∀ j, IsIso ((F j).map φ) := fun j => by
    letI := h j.down
    exact overFunctorMap_isIso_of_restrictMap_isIso (p3StandardOpen (K := K) j.down) φ
  exact hF.isIso φ

/-- Native O(3) tensor O(-4) is the actual O(-1). -/
theorem p3ThreePositiveFourNegativePairing_isIso :
    IsIso (positiveNegativeDifferencePairing PS 3 4 p3PairingIso_three_le_four) := by
  apply p3Hom_isIso_of_coordinate_restrictions K
  intro j
  let U := p3StandardOpen (K := K) j
  let R := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p3Coordinate K j) 1
  letI : IsIso (R.map (positiveMulHomogeneous PS s 3)) :=
    p3PositiveMulCoordinatePower_isIso K j 1 (by decide) 3
  letI : IsIso (R.map (mulHomogeneous PS s 0)) :=
    restrict_mulCoordinatePower_isIso K j 1 (by decide)
  letI : IsIso (R.map (positiveNegativePairing PS 4)) :=
    p3CoordinatePositiveNegativePairing_isIso K j 4
  letI : IsIso (R.map (schemeModuleTensorMap (positiveMulHomogeneous PS s 3)
      (𝟙 (sheafOfModules PS 4)))) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous PS s 3) (𝟙 (sheafOfModules PS 4))
  have h := congrArg R.map
    (positiveNegativeDifferencePairing_three_four_mul_naturality PS s)
  rw [R.map_comp, R.map_comp] at h
  haveI : IsIso (R.map (positiveNegativeDifferencePairing PS 3 4 p3PairingIso_three_le_four) ≫
      R.map (mulHomogeneous PS s 0)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (R.map (positiveNegativeDifferencePairing PS 3 4 p3PairingIso_three_le_four))
    (R.map (mulHomogeneous PS s 0))

/-- Native O(3) tensor O(-6) is the actual O(-3). -/
theorem p3ThreePositiveSixNegativePairing_isIso :
    IsIso (positiveNegativeDifferencePairing PS 3 6 p3PairingIso_three_le_six) := by
  apply p3Hom_isIso_of_coordinate_restrictions K
  intro j
  let U := p3StandardOpen (K := K) j
  let R := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p3Coordinate K j) 3
  letI : IsIso (R.map (positiveMulHomogeneous PS s 3)) :=
    p3PositiveMulCoordinatePower_isIso K j 3 (by decide) 3
  letI : IsIso (R.map (mulHomogeneous PS s 0)) :=
    restrict_mulCoordinatePower_isIso K j 3 (by decide)
  letI : IsIso (R.map (positiveNegativePairing PS 6)) :=
    p3CoordinatePositiveNegativePairing_isIso K j 6
  letI : IsIso (R.map (schemeModuleTensorMap (positiveMulHomogeneous PS s 3)
      (𝟙 (sheafOfModules PS 6)))) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous PS s 3) (𝟙 (sheafOfModules PS 6))
  have h := congrArg R.map
    (positiveNegativeDifferencePairing_three_six_mul_naturality PS s)
  rw [R.map_comp, R.map_comp] at h
  haveI : IsIso (R.map (positiveNegativeDifferencePairing PS 3 6 p3PairingIso_three_le_six) ≫
      R.map (mulHomogeneous PS s 0)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (R.map (positiveNegativeDifferencePairing PS 3 6 p3PairingIso_three_le_six))
    (R.map (mulHomogeneous PS s 0))

/-- The positive-result equal-degree pairing is also the actual inverse
pairing, with actual zero positive twist identified internally. -/
private theorem p3ThreePositiveThreeNegativePositivePairing_isIso :
    IsIso (positiveNegativePositiveDifferencePairing PS 3 3 p3PairingIso_three_le_three) := by
  letI : IsIso (positiveZeroToZeroTwist PS) := (positiveZeroTwistIso PS).isIso_hom
  letI : IsIso (positiveNegativePairing PS 3) := p3PositiveNegativePairing_isIso K 3
  haveI : IsIso (positiveNegativePositiveDifferencePairing PS 3 3 p3PairingIso_three_le_three ≫
      positiveZeroToZeroTwist PS) := by
    rw [positiveNegativePositiveDifferencePairing_three_three_factorization]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (positiveNegativePositiveDifferencePairing PS 3 3 p3PairingIso_three_le_three) (positiveZeroToZeroTwist PS)

/-- Native O(3) tensor O(-2) is the actual positive O(1). -/
theorem p3ThreePositiveTwoNegativePairing_isIso :
    IsIso (positiveNegativePositiveDifferencePairing PS 3 2 p3PairingIso_two_le_three) := by
  apply p3Hom_isIso_of_coordinate_restrictions K
  intro j
  let U := p3StandardOpen (K := K) j
  let R := Scheme.Modules.restrictFunctor U.ι
  let s := p3Coordinate K j
  letI : IsIso (R.map (mulHomogeneous PS s 2)) := by
    exact restrict_mulHomogeneous_isIso_on_basicOpen PS s 2
      (mvPolynomial_irrelevant_le_span_degreeOne_small (K := K) (σ := Fin 4))
  letI : IsIso (R.map (positiveMulHomogeneous PS s 0)) := by
    exact restrict_positiveMulHomogeneous_isIso_on_basicOpen PS s 0
      (mvPolynomial_irrelevant_le_span_degreeOne_small (K := K) (σ := Fin 4))
  letI : IsIso (positiveNegativePositiveDifferencePairing PS 3 3 p3PairingIso_three_le_three) :=
    p3ThreePositiveThreeNegativePositivePairing_isIso K
  letI : IsIso (R.map (schemeModuleTensorMap (𝟙 (positiveSheafOfModules PS 3))
      (mulHomogeneous PS s 2))) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U
      (𝟙 (positiveSheafOfModules PS 3)) (mulHomogeneous PS s 2)
  have h := congrArg R.map
    (positiveNegativePositiveDifferencePairing_three_two_mul_naturality PS s)
  rw [R.map_comp, R.map_comp] at h
  haveI : IsIso (R.map (schemeModuleTensorMap (𝟙 (positiveSheafOfModules PS 3))
      (mulHomogeneous PS s 2)) ≫
      R.map (positiveNegativePositiveDifferencePairing PS 3 2 p3PairingIso_two_le_three)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (R.map (schemeModuleTensorMap (𝟙 (positiveSheafOfModules PS 3)) (mulHomogeneous PS s 2)))
    (R.map (positiveNegativePositiveDifferencePairing PS 3 2 p3PairingIso_two_le_three))

/-- Actual right-order tensor term Iso O(-6) tensor O(3) ≅ O(-3). -/
def p3OThreeTensorNegativeSixIso :
    schemeModuleTensor (sheafOfModules PS 6) (positiveSheafOfModules PS 3) ≅
      sheafOfModules PS 3 := by
  letI := p3ThreePositiveSixNegativePairing_isIso K
  exact schemeModuleTensorSymmetry _ _ ≪≫
    asIso (positiveNegativeDifferencePairing PS 3 6 p3PairingIso_three_le_six)

/-- Actual right-order tensor term Iso O(-4) tensor O(3) ≅ O(-1). -/
def p3OThreeTensorNegativeFourIso :
    schemeModuleTensor (sheafOfModules PS 4) (positiveSheafOfModules PS 3) ≅
      sheafOfModules PS 1 := by
  letI := p3ThreePositiveFourNegativePairing_isIso K
  exact schemeModuleTensorSymmetry _ _ ≪≫
    asIso (positiveNegativeDifferencePairing PS 3 4 p3PairingIso_three_le_four)

/-- Actual right-order tensor term Iso O(-2) tensor O(3) ≅ O(1). -/
def p3OThreeTensorNegativeTwoIso :
    schemeModuleTensor (sheafOfModules PS 2) (positiveSheafOfModules PS 3) ≅
      positiveSheafOfModules PS 1 := by
  letI := p3ThreePositiveTwoNegativePairing_isIso K
  exact schemeModuleTensorSymmetry _ _ ≪≫
    asIso (positiveNegativePositiveDifferencePairing PS 3 2 p3PairingIso_two_le_three)

end PfaffianDescent.ProjectiveNegativeTwist

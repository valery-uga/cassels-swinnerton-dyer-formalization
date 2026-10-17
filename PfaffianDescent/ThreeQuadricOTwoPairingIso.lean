import PfaffianDescent.ThreeQuadricOTwoPairingNaturality

/-! SOURCE ONLY / UNVERIFIED. Native mixed pairing isomorphisms for the
actual O(2)-twisted quadric Koszul terms. Coordinate-power naturality and
actual local invertibility derive all tensor identifications internally. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem p3OTwoPairingIso_two_le_four : (2 : ℕ) ≤ 4 := by decide
private theorem p3OTwoPairingIso_two_le_six : (2 : ℕ) ≤ 6 := by decide
private theorem p3OTwoPairingIso_two_le_two : (2 : ℕ) ≤ 2 := le_rfl

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

/-- Native O(2) tensor O(-4) is the actual O(-2). -/
theorem p3TwoPositiveFourNegativePairing_isIso :
    IsIso (positiveNegativeDifferencePairing PS 2 4 p3OTwoPairingIso_two_le_four) := by
  apply p3Hom_isIso_of_coordinate_restrictions K
  intro j
  let U := p3StandardOpen (K := K) j
  let R := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p3Coordinate K j) 2
  letI : IsIso (R.map (positiveMulHomogeneous PS s 2)) :=
    p3PositiveMulCoordinatePower_isIso K j 2 (by decide) 2
  letI : IsIso (R.map (mulHomogeneous PS s 0)) :=
    restrict_mulCoordinatePower_isIso K j 2 (by decide)
  letI : IsIso (R.map (positiveNegativePairing PS 4)) :=
    p3CoordinatePositiveNegativePairing_isIso K j 4
  letI : IsIso (R.map (schemeModuleTensorMap (positiveMulHomogeneous PS s 2)
      (𝟙 (sheafOfModules PS 4)))) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous PS s 2) (𝟙 (sheafOfModules PS 4))
  have h := congrArg R.map
    (positiveNegativeDifferencePairing_two_four_mul_naturality PS s)
  rw [R.map_comp, R.map_comp] at h
  haveI : IsIso (R.map (positiveNegativeDifferencePairing PS 2 4 p3OTwoPairingIso_two_le_four) ≫
      R.map (mulHomogeneous PS s 0)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (R.map (positiveNegativeDifferencePairing PS 2 4 p3OTwoPairingIso_two_le_four))
    (R.map (mulHomogeneous PS s 0))

/-- Native O(2) tensor O(-6) is the actual O(-4). -/
theorem p3TwoPositiveSixNegativePairing_isIso :
    IsIso (positiveNegativeDifferencePairing PS 2 6 p3OTwoPairingIso_two_le_six) := by
  apply p3Hom_isIso_of_coordinate_restrictions K
  intro j
  let U := p3StandardOpen (K := K) j
  let R := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p3Coordinate K j) 4
  letI : IsIso (R.map (positiveMulHomogeneous PS s 2)) :=
    p3PositiveMulCoordinatePower_isIso K j 4 (by decide) 2
  letI : IsIso (R.map (mulHomogeneous PS s 0)) :=
    restrict_mulCoordinatePower_isIso K j 4 (by decide)
  letI : IsIso (R.map (positiveNegativePairing PS 6)) :=
    p3CoordinatePositiveNegativePairing_isIso K j 6
  letI : IsIso (R.map (schemeModuleTensorMap (positiveMulHomogeneous PS s 2)
      (𝟙 (sheafOfModules PS 6)))) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous PS s 2) (𝟙 (sheafOfModules PS 6))
  have h := congrArg R.map
    (positiveNegativeDifferencePairing_two_six_mul_naturality PS s)
  rw [R.map_comp, R.map_comp] at h
  haveI : IsIso (R.map (positiveNegativeDifferencePairing PS 2 6 p3OTwoPairingIso_two_le_six) ≫
      R.map (mulHomogeneous PS s 0)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (R.map (positiveNegativeDifferencePairing PS 2 6 p3OTwoPairingIso_two_le_six))
    (R.map (mulHomogeneous PS s 0))

/-- The positive-result equal-degree pairing is also the actual inverse
pairing, with actual zero positive twist identified internally. -/
theorem p3TwoPositiveTwoNegativePositivePairing_isIso :
    IsIso (positiveNegativePositiveDifferencePairing PS 2 2 p3OTwoPairingIso_two_le_two) := by
  letI : IsIso (positiveZeroToZeroTwist PS) := (positiveZeroTwistIso PS).isIso_hom
  letI : IsIso (positiveNegativePairing PS 2) := p3PositiveNegativePairing_isIso K 2
  haveI : IsIso (positiveNegativePositiveDifferencePairing PS 2 2 p3OTwoPairingIso_two_le_two ≫
      positiveZeroToZeroTwist PS) := by
    rw [positiveNegativePositiveDifferencePairing_two_two_factorization]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (positiveNegativePositiveDifferencePairing PS 2 2 p3OTwoPairingIso_two_le_two) (positiveZeroToZeroTwist PS)


/-- Actual structure sheaf to the canonical positive zero twist. -/
def p3OTwoUnitPositiveZeroIso :
    SheafOfModules.unit (Proj PS).ringCatSheaf ≅ positiveSheafOfModules PS 0 :=
  unitIsoZeroTwist PS ≪≫ (positiveZeroTwistIso PS).symm

/-- The actual O(-6) tensor O(2) is O(-4). -/
def p3OTwoTensorNegativeSixIso :
    schemeModuleTensor (sheafOfModules PS 6) (positiveSheafOfModules PS 2) ≅
      sheafOfModules PS 4 := by
  letI := p3TwoPositiveSixNegativePairing_isIso K
  exact schemeModuleTensorSymmetry _ _ ≪≫
    asIso (positiveNegativeDifferencePairing PS 2 6 p3OTwoPairingIso_two_le_six)

/-- The actual O(-4) tensor O(2) is O(-2). -/
def p3OTwoTensorNegativeFourIso :
    schemeModuleTensor (sheafOfModules PS 4) (positiveSheafOfModules PS 2) ≅
      sheafOfModules PS 2 := by
  letI := p3TwoPositiveFourNegativePairing_isIso K
  exact schemeModuleTensorSymmetry _ _ ≪≫
    asIso (positiveNegativeDifferencePairing PS 2 4 p3OTwoPairingIso_two_le_four)

/-- The actual O(-2) tensor O(2) is the actual structure sheaf. -/
def p3OTwoTensorNegativeTwoIso :
    schemeModuleTensor (sheafOfModules PS 2) (positiveSheafOfModules PS 2) ≅
      SheafOfModules.unit (Proj PS).ringCatSheaf := by
  letI := p3TwoPositiveTwoNegativePositivePairing_isIso K
  exact schemeModuleTensorSymmetry _ _ ≪≫
    asIso (positiveNegativePositiveDifferencePairing PS 2 2 p3OTwoPairingIso_two_le_two) ≪≫
    (p3OTwoUnitPositiveZeroIso K).symm

end PfaffianDescent.ProjectiveNegativeTwist

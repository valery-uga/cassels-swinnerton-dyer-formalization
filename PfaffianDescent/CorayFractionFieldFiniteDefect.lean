import PfaffianDescent.CorayAffineGlobalNormalizationDefect
import PfaffianDescent.CorayNormalizationDefectLocalizationComparison

/-! Actual scalar-preserving ambient fraction field and finite affine defect.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray

/-- The canonical fraction-ring algebra equivalence induces an ORIGINAL
A-linear equivalence on the literal normalization quotient. -/
def normalizationDefectFractionRingEquiv
    (A F : Type*) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] :
    localNormalizationDefect A (FractionRing A) ≃ₗ[A] localNormalizationDefect A F :=
  normalizationDefectAmbientEquiv (FractionRing.algEquiv (A := A) F)

/-- The literal defect inside the ACTUAL ambient fraction field has finite
ORIGINAL ground dimension, transported by the actual A-algebra equivalence. -/
theorem finiteTypeCurve_normalizationDefect_finite_over_ground_in_fractionField
    (K A F : Type*) [Field K] [CharZero K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] [Ring.DimensionLEOne A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra K F] [IsScalarTower K A F] :
    Module.Finite K (localNormalizationDefect A F) := by
  letI : Module.Finite K (localNormalizationDefect A (FractionRing A)) :=
    finiteTypeCurve_normalizationDefect_finite_over_ground K A
  exact Module.Finite.equiv ((normalizationDefectFractionRingEquiv A F).restrictScalars K)

/-- The literal defect in the ACTUAL ambient fraction field has actual finite
module support; finite normalization and actual torsion are derived internally. -/
theorem finiteTypeCurve_normalizationDefect_support_finite_in_fractionField
    (K A F : Type*) [Field K] [CharZero K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] [Ring.DimensionLEOne A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    (Module.support A (localNormalizationDefect A F)).Finite := by
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  letI : Module.Finite A (integralClosure A (FractionRing A)) :=
    finiteNormalization_of_finiteType_charZero K A
  letI : Module.Finite A (integralClosure A F) :=
    Module.Finite.equiv (FractionRing.algEquiv (A := A) F).mapIntegralClosure.toLinearEquiv
  letI : Module.Finite A (localNormalizationDefect A F) := inferInstance
  exact finiteTorsion_support_finite A (localNormalizationDefect A F)
    (localNormalizationDefect_isTorsion A F)

end PfaffianDescent.Coray

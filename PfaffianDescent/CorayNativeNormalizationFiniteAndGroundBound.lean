import PfaffianDescent.CorayNormalizationDefectNativeLocalization
import PfaffianDescent.CorayFiniteGroundLocalization
import PfaffianDescent.CorayNonregularLocalNormalizationDegreeContribution
import Mathlib.RingTheory.Localization.Finiteness

/-! SOURCE ONLY / UNVERIFIED. Finite native normalization is derived from
finite affine normalization in the SAME field. The native localization
comparison is consumed from the separate scalar-worker packet, not repeated.
Every ground action below is explicit restriction through its actual ring. -/
noncomputable section
namespace PfaffianDescent.Coray
open Algebra Module IsLocalRing
open scoped nonZeroDivisors
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- Integral closure in the same field is finite after an ACTUAL ring
localization, with no finite-native-normalization premise. -/
theorem integralClosure_nativeLocalization_finite
    (A R F : Type*) [CommRing A] [IsDomain A] [CommRing R] [Field F]
    [Algebra A F] [IsFractionRing A F]
    (S : Submonoid A) (hS : S ≤ A⁰)
    [Algebra A R] [IsLocalization S R] [Algebra R F] [IsScalarTower A R F]
    [Module.Finite A (integralClosure A F)] :
    Module.Finite R (integralClosure R F) := by
  letI : IsLocalization (Algebra.algebraMapSubmonoid F S) F := by
    apply IsLocalization.of_le_isUnit
    rintro f ⟨a, ha, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    apply (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr
    exact mem_nonZeroDivisors_iff_ne_zero.mp (hS ha)
  let i : integralClosure A F →ₐ[A] integralClosure R F :=
    (integralClosure A F).val.codRestrict ((integralClosure R F).restrictScalars A)
      (fun y => y.property.tower_top)
  letI : Algebra (integralClosure A F) (integralClosure R F) := i.toRingHom.toAlgebra
  letI : IsScalarTower A (integralClosure A F) (integralClosure R F) :=
    IsScalarTower.of_algebraMap_eq (fun a => (i.commutes a).symm)
  letI : IsScalarTower (integralClosure A F) (integralClosure R F) F :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A F) S)
      (integralClosure R F) :=
    IsLocalization.integralClosure (R := A) (S := F) (Rf := R) (Sf := F) S
  exact Module.Finite.of_isLocalization A (integralClosure A F) S

/-- Both actions are restriction along original ring maps. A compatible
K->A->R tower makes the actual native defect a quotient of the finite
original affine defect over K; no dimension inequality is a hypothesis. -/
theorem normalizationDefect_nativeLocalization_originalGround_finrank_le
    (K A R F : Type*) [Field K] [CommRing A] [IsDomain A] [CommRing R] [Field F]
    [Algebra K A] [Algebra K R] [Algebra A R] [IsScalarTower K A R]
    [Algebra A F] [IsFractionRing A F]
    (S : Submonoid A) (hS : S ≤ A⁰)
    [IsLocalization S R] [Algebra R F] [IsScalarTower A R F] :
    letI : Module K (localNormalizationDefect A F) :=
      Module.compHom _ (algebraMap K A)
    letI : Module K (localNormalizationDefect R F) :=
      Module.compHom _ (algebraMap K R)
    Module.Finite K (localNormalizationDefect A F) →
      Module.Finite K (localNormalizationDefect R F) ∧
        finrank K (localNormalizationDefect R F) ≤
          finrank K (localNormalizationDefect A F) := by
  letI : Module K (localNormalizationDefect A F) := Module.compHom _ (algebraMap K A)
  letI : Module K (localNormalizationDefect R F) := Module.compHom _ (algebraMap K R)
  intro hfinite
  letI : Module.Finite K (localNormalizationDefect A F) := hfinite
  letI : IsScalarTower K A (localNormalizationDefect A F) := IsScalarTower.of_compHom K A _
  letI : IsScalarTower K R (localNormalizationDefect R F) := IsScalarTower.of_compHom K R _
  letI : IsScalarTower K A (localNormalizationDefect R F) := by
    apply IsScalarTower.of_algebraMap_smul
    intro c z
    change algebraMap K A c • z = algebraMap K R c • z
    rw [IsScalarTower.algebraMap_apply K A R]
    exact (IsScalarTower.algebraMap_smul (R := A) (A := R) (algebraMap K A c) z).symm
  let e := (normalizationDefectLocalizationEquiv_native_commonField A R F S hS).restrictScalars A
  let m := LocalizedModule.mkLinearMap S (localNormalizationDefect A F)
  let f := e.toLinearMap.comp m
  letI : IsLocalizedModule S f := IsLocalizedModule.of_linearEquiv S m e
  exact groundFinite_localization_finite_and_finrank_le S f

/-- Nonregularity contributes the OWN full residue weight under explicit
restriction through K->R. No ambient-field ground algebra is needed, and
no quotient-sheaf stalk identification is part of this local assertion. -/
theorem localNormalizationDefect_nonregular_restrictedGround_degree_lower_bound
    (K R F : Type*) [Field K] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] [Ring.DimensionLEOne R] [Algebra K R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Module.Finite K (ResidueField R)] [Module.Finite R (integralClosure R F)]
    (hsing : ¬ IsRegularLocalRing R) :
    letI : Module K (localNormalizationDefect R F) := Module.compHom _ (algebraMap K R)
    finrank K (ResidueField R) ≤ finrank K (localNormalizationDefect R F) := by
  letI : Module K (localNormalizationDefect R F) := Module.compHom _ (algebraMap K R)
  letI : IsScalarTower K R (localNormalizationDefect R F) := IsScalarTower.of_compHom K R _
  letI := localNormalizationDefect_nontrivial_of_not_isRegularLocalRing R F hsing
  have hlength := localNormalizationDefect_isFiniteLength_of_finiteNormalization R F
  have hneTop := Module.length_ne_top_iff.mpr hlength
  have hpos : 0 < Module.length R (localNormalizationDefect R F) := Module.length_pos
  have hlower : 1 ≤ (Module.length R (localNormalizationDefect R F)).toNat :=
    ENat.toNat_pos (ne_of_gt hpos) hneTop
  have hweight := localModule_ground_finrank_eq_residue_weight
    (K := K) (R := R) (N := localNormalizationDefect R F) hlength
  calc
    finrank K (ResidueField R) = 1 * finrank K (ResidueField R) := (one_mul _).symm
    _ ≤ (Module.length R (localNormalizationDefect R F)).toNat *
        finrank K (ResidueField R) := Nat.mul_le_mul_right _ hlower
    _ = finrank K (localNormalizationDefect R F) := hweight.symm

end PfaffianDescent.Coray

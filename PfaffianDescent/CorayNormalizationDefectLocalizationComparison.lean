import PfaffianDescent.CorayLocalNormalizationDefect
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Support

/-!
# Localization of the literal normalization quotient

The affine normalization quotient localized at a prime is canonically
isomorphic to the literal normalization defect of the prime localization.
This uses the actual integral-closure localization theorem and the actual
quotient-localization universal property. No comparison certificate,
finiteness, dimension, characteristic, or genus premise is supplied.

STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray
open Algebra Module
open scoped nonZeroDivisors

/-- Localizing the image of the ground ring gives exactly the image of the
localized ground ring. This identifies the denominator submodule, not merely
its abstract isomorphism class. -/
theorem localized_algebraRange_eq
    {A D E : Type*} [CommRing A] [CommRing D] [CommRing E]
    [Algebra A D] [Algebra A E]
    (S : Submonoid A) [Algebra (Localization S) E]
    [IsScalarTower A (Localization S) E]
    (i : D →ₐ[A] E) [IsLocalizedModule S i.toLinearMap] :
    (LinearMap.range (Algebra.linearMap A D)).localized'
        (Localization S) S i.toLinearMap =
      LinearMap.range (Algebra.linearMap (Localization S) E) := by
  rw [Submodule.localized'_eq_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨z, ⟨a, rfl⟩, rfl⟩
    refine ⟨algebraMap A (Localization S) a, ?_⟩
    change algebraMap (Localization S) E (algebraMap A (Localization S) a) =
      i (algebraMap A D a)
    exact (IsScalarTower.algebraMap_apply A (Localization S) E a).symm.trans
      (i.commutes a).symm
  · rintro y ⟨l, rfl⟩
    have h1 : (1 : E) ∈ Submodule.span (Localization S)
        (i.toLinearMap '' (LinearMap.range (Algebra.linearMap A D) : Set D)) := by
      apply Submodule.subset_span
      refine ⟨1, ⟨1, by simp⟩, by simp⟩
    have h := (Submodule.span (Localization S)
      (i.toLinearMap '' (LinearMap.range (Algebra.linearMap A D) : Set D))).smul_mem l h1
    change algebraMap (Localization S) E l ∈ Submodule.span (Localization S)
      (i.toLinearMap '' (LinearMap.range (Algebra.linearMap A D) : Set D))
    simpa only [Algebra.smul_def, mul_one] using h

/-- The quotient by the ring image commutes with an actual module
localization. Its target is the literal quotient by the localized ring image. -/
def algebraRangeQuotientLocalizationEquiv
    {A D E : Type*} [CommRing A] [CommRing D] [CommRing E]
    [Algebra A D] [Algebra A E]
    (S : Submonoid A) [Algebra (Localization S) E]
    [IsScalarTower A (Localization S) E]
    (i : D →ₐ[A] E) [IsLocalizedModule S i.toLinearMap] :
    LocalizedModule S (D ⧸ LinearMap.range (Algebra.linearMap A D)) ≃ₗ[Localization S]
      E ⧸ LinearMap.range (Algebra.linearMap (Localization S) E) := by
  let N := LinearMap.range (Algebra.linearMap A D)
  let q := N.toLocalizedQuotient' (Localization S) S i.toLinearMap
  let e := (IsLocalizedModule.iso S q).extendScalarsOfIsLocalization S (Localization S)
  exact e.trans (Submodule.quotEquivOfEq _ _ (localized_algebraRange_eq S i))

/-- An actual algebra equivalence of ambient fields carries the actual
normalization quotient to the actual normalization quotient. -/
def normalizationDefectAmbientEquiv
    {R F G : Type*} [CommRing R] [Field F] [Field G]
    [Algebra R F] [Algebra R G] (e : F ≃ₐ[R] G) :
    localNormalizationDefect R F ≃ₗ[R] localNormalizationDefect R G := by
  let f := e.mapIntegralClosure
  apply Submodule.Quotient.equiv _ _ f.toLinearEquiv
  apply le_antisymm
  · rintro y ⟨z, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, (f.commutes r).symm⟩
  · rintro y ⟨r, rfl⟩
    refine ⟨algebraMap R (integralClosure R F) r, ⟨r, rfl⟩, ?_⟩
    exact f.commutes r

/-- The actual normalization localized at a prime, first expressed inside
the same ambient fraction field as the global normalization. -/
def normalizationDefectLocalizationEquiv_commonFractionField
    (A : Type*) [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] :
    LocalizedModule.AtPrime P (localNormalizationDefect A (FractionRing A)) ≃ₗ[Localization.AtPrime P]
      localNormalizationDefect (Localization.AtPrime P) (FractionRing A) := by
  let L := Localization.AtPrime P
  let F := FractionRing A
  letI : IsLocalization (Algebra.algebraMapSubmonoid F P.primeCompl) F := by
    apply IsLocalization.of_le_isUnit
    rintro f ⟨a, ha, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    apply (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr
    exact mem_nonZeroDivisors_iff_ne_zero.mp (P.primeCompl_le_nonZeroDivisors ha)
  let i : integralClosure A F →ₐ[A] integralClosure L F :=
    (integralClosure A F).val.codRestrict ((integralClosure L F).restrictScalars A)
      (fun y => y.property.tower_top)
  letI : Algebra (integralClosure A F) (integralClosure L F) := i.toRingHom.toAlgebra
  letI : IsScalarTower A (integralClosure A F) (integralClosure L F) :=
    IsScalarTower.of_algebraMap_eq (fun a => (i.commutes a).symm)
  letI : IsScalarTower (integralClosure A F) (integralClosure L F) F :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A F) P.primeCompl)
      (integralClosure L F) :=
    IsLocalization.integralClosure (R := A) (S := F) (Rf := L) (Sf := F) P.primeCompl
  letI : IsLocalizedModule P.primeCompl i.toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  exact algebraRangeQuotientLocalizationEquiv P.primeCompl i

/-- The affine global normalization defect localized at an actual prime is
canonically the literal local normalization defect, including its actual
fraction-field presentation. No comparison is assumed. -/
def normalizationDefectLocalizationEquiv
    (A : Type*) [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] :
    LocalizedModule.AtPrime P (localNormalizationDefect A (FractionRing A)) ≃ₗ[Localization.AtPrime P]
      localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) :=
  (normalizationDefectLocalizationEquiv_commonFractionField A P).trans
    (normalizationDefectAmbientEquiv (FractionRing.algEquiv
      (A := Localization.AtPrime P) (FractionRing A)).symm)

/-- The actual comparison preserves nontriviality of the two literal
quotient modules. -/
theorem normalizationDefectLocalization_nontrivial_iff
    (A : Type*) [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] :
    Nontrivial (LocalizedModule.AtPrime P (localNormalizationDefect A (FractionRing A))) ↔
      Nontrivial (localNormalizationDefect (Localization.AtPrime P)
        (FractionRing (Localization.AtPrime P))) :=
  (normalizationDefectLocalizationEquiv A P).toEquiv.nontrivial_congr

/-- Support of the literal affine defect is exactly the locus where the
literal local normalization defect is nonzero. -/
theorem mem_normalizationDefect_support_iff
    (A : Type*) [CommRing A] [IsDomain A] (P : PrimeSpectrum A) :
    P ∈ Module.support A (localNormalizationDefect A (FractionRing A)) ↔
      Nontrivial (localNormalizationDefect (Localization.AtPrime P.asIdeal)
        (FractionRing (Localization.AtPrime P.asIdeal))) := by
  rw [Module.mem_support_iff]
  exact normalizationDefectLocalization_nontrivial_iff A P.asIdeal

end PfaffianDescent.Coray

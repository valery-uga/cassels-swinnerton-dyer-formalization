import PfaffianDescent.CorayLocalNormalizationDefect
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Actual conductor and finite composition length of normalization defect

Every literal defect class is killed by an actual nonzero fraction denominator.
For an actual finite normalization module, an actual common nonzero annihilator
exists. Over a Noetherian domain of dimension at most one, the corresponding
quotient ring has all primes maximal, hence is Artinian. Its actual finite
module is Artinian, giving genuine finite composition length of the defect.

No finite-length, conductor, torsion or Artinian certificate is supplied.
Finiteness of the actual normalization is the earlier proved prerequisite;
actual curve wrappers below derive that prerequisite internally.

STATUS: UNVERIFIED source only; root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open Algebra Module IsLocalRing
open scoped nonZeroDivisors

/-- Every literal normalization-defect class is killed by an actual nonzero
fraction denominator. This torsion conclusion requires no finite module. -/
theorem localNormalizationDefect_isTorsion
    (R F : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] :
    Module.IsTorsion R (localNormalizationDefect R F) := by
  let D := integralClosure R F
  let S : Submodule R D := LinearMap.range (Algebra.linearMap R D)
  intro z
  obtain ⟨y, rfl⟩ := S.mkQ_surjective z
  obtain ⟨⟨a, b⟩, heq⟩ := IsLocalization.surj R⁰ (y : F)
  have hy : (b : R) • y ∈ S := by
    refine ⟨a, ?_⟩
    apply Subtype.ext
    simpa only [Algebra.linearMap_apply, Subalgebra.coe_algebraMap,
      Subalgebra.coe_smul, Subalgebra.coe_mul, Algebra.smul_def] using heq.symm.trans (mul_comm _ _)
  refine ⟨b, ?_⟩
  change (b : R) • S.mkQ y = 0
  rw [← map_smul]
  exact (Submodule.Quotient.mk_eq_zero S).mpr hy

/-- The literal conductor ideal of the literal normalization quotient. -/
def normalizationConductor
    (R F : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] : Ideal R :=
  (⊤ : Submodule R (localNormalizationDefect R F)).annihilator

/-- Conductor membership means multiplication of every actual integral
fraction lands in the actual original-ring image. -/
theorem normalizationConductor_mem_iff
    (R F : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (a : R) :
    a ∈ normalizationConductor R F ↔
      ∀ y : integralClosure R F,
        a • y ∈ LinearMap.range (Algebra.linearMap R (integralClosure R F)) := by
  let S : Submodule R (integralClosure R F) :=
    LinearMap.range (Algebra.linearMap R (integralClosure R F))
  constructor
  · intro ha y
    have hz : a • S.mkQ y = 0 := Submodule.mem_annihilator.mp ha _ (by trivial)
    have hzero : S.mkQ (a • y) = 0 := by simpa only [map_smul] using hz
    exact (Submodule.Quotient.mk_eq_zero S).mp hzero
  · intro h
    apply Submodule.mem_annihilator.mpr
    intro z hz
    obtain ⟨y, rfl⟩ := S.mkQ_surjective z
    have hzero : S.mkQ (a • y) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr (h y)
    simpa only [map_smul] using hzero

/-- Actual finite normalization has an actual common nonzero conductor. -/
theorem normalizationConductor_exists_nonzero_of_finiteNormalization
    (R F : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]
    [Module.Finite R (integralClosure R F)] :
    ∃ a : R, a ∈ normalizationConductor R F ∧ a ≠ 0 := by
  letI : Module.Finite R (localNormalizationDefect R F) := inferInstance
  obtain ⟨a, ha, hregular⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (localNormalizationDefect_isTorsion R F)
  exact ⟨a, ha, mem_nonZeroDivisors_iff_ne_zero.mp hregular⟩

/-- Any finite torsion module over a Noetherian domain of dimension at most
one has actual finite composition length. The Artinian annihilator quotient
is proved from actual nonzero annihilator and actual prime ideals. -/
theorem finiteTorsion_isFiniteLength_of_dimensionLEOne
    (R N : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (htorsion : Module.IsTorsion R N) : IsFiniteLength R N := by
  let I : Ideal R := (⊤ : Submodule R N).annihilator
  obtain ⟨a, ha, hregular⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htorsion
  have hane : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hregular
  let S := R ⧸ I
  letI : Ring.KrullDimLE 0 S := Ring.KrullDimLE.mk₀ (fun J hJ => by
    have hprime : (J.comap (Ideal.Quotient.mk I)).IsPrime := hJ.comap _
    have hamem : a ∈ J.comap (Ideal.Quotient.mk I) := by
      change Ideal.Quotient.mk I a ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact J.zero_mem
    have hnonzero : J.comap (Ideal.Quotient.mk I) ≠ ⊥ := by
      intro hbot
      rw [hbot, Ideal.mem_bot] at hamem
      exact hane hamem
    have hmax := hprime.isMaximal hnonzero
    have hmap := Ideal.map_eq_top_or_isMaximal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hmax
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective J] at hmap
    exact hmap.resolve_left hJ.ne_top)
  letI : IsArtinianRing S := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let hkill : Module.IsTorsionBySet R N I := Module.isTorsionBySet_annihilator_top R N
  letI : Module S N := hkill.module
  letI : IsScalarTower R S N := hkill.isScalarTower
  letI : Module.Finite S N := Module.Finite.of_restrictScalars_finite R S N
  letI : IsArtinian S N := inferInstance
  letI : IsArtinian R N := isArtinian_of_surjective_algebraMap (R := S) (S := R)
    (M := N) Ideal.Quotient.mk_surjective
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- Finite normalization gives genuine finite COMPOSITION length of the
literal defect over a Noetherian domain of dimension at most one. -/
theorem localNormalizationDefect_isFiniteLength_of_finiteNormalization
    (R F : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] [Field F] [Algebra R F] [IsFractionRing R F]
    [Module.Finite R (integralClosure R F)] :
    IsFiniteLength R (localNormalizationDefect R F) := by
  letI : Module.Finite R (localNormalizationDefect R F) := inferInstance
  exact finiteTorsion_isFiniteLength_of_dimensionLEOne R (localNormalizationDefect R F)
    (localNormalizationDefect_isTorsion R F)

/-- The actual ENat composition length of the literal defect is finite. -/
theorem localNormalizationDefect_length_ne_top_of_finiteNormalization
    (R F : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] [Field F] [Algebra R F] [IsFractionRing R F]
    [Module.Finite R (integralClosure R F)] :
    Module.length R (localNormalizationDefect R F) ≠ ⊤ :=
  Module.length_ne_top_iff.mpr
    (localNormalizationDefect_isFiniteLength_of_finiteNormalization R F)

end PfaffianDescent.Coray

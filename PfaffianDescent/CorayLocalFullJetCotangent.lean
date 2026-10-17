import PfaffianDescent.CorayLocalNormalizationDefect
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Actual full jets force large local cotangent rank

A surjection from a local ring to the two-direction first-jet algebra forces
its maximal ideal to be nonprincipal. The actual cotangent rank is therefore
at least two over that ring's own residue field. We do not identify this
residue field with the supplied jet field by an unproved certificate.

The actual full jet extends to the localization at its literal residue kernel.
For a one-dimensional local domain the proved rank bound supplies the actual
normalization defect theorem's input. Domain and dimension hypotheses for a
particular geometric curve are separate, explicitly outstanding steps.

STATUS: UNVERIFIED source draft. Root owns all compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open TrivSqZeroExt IsLocalRing Module

universe u v
variable {R : Type u} [CommRing R] {M : Type v} [Field M]

/-- The actual residue map of the actual full jet. -/
def fullJetResidueMap (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) : R →+* M :=
  (TrivSqZeroExt.fstHom M M (Fin 2 → M)).toRingHom.comp φ

theorem fullJetResidueMap_surjective
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) (hφ : Function.Surjective φ) :
    Function.Surjective (fullJetResidueMap φ) := by
  intro a
  obtain ⟨r, hr⟩ := hφ (inl a)
  exact ⟨r, by change (φ r).fst = a; rw [hr]; rfl⟩

/-- Actual full-jet basis preimages prevent a principal maximal ideal. -/
theorem maximalIdeal_not_principal_of_surjective_fullJet
    [IsLocalRing R]
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) (hφ : Function.Surjective φ) :
    ¬ (maximalIdeal R).IsPrincipal := by
  classical
  intro hprincipal
  obtain ⟨g, hg : maximalIdeal R = Ideal.span {g}⟩ := hprincipal.1
  have hker : RingHom.ker (fullJetResidueMap φ) = maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal (fullJetResidueMap φ)
      (fullJetResidueMap_surjective φ hφ)
  have hgmem : g ∈ maximalIdeal R := by
    rw [hg]
    exact Ideal.subset_span (Set.mem_singleton g)
  have hgzero : (φ g).fst = 0 := by
    change g ∈ RingHom.ker (fullJetResidueMap φ)
    rw [hker]
    exact hgmem
  obtain ⟨r₀, hr₀⟩ := hφ (inr (Pi.single (0 : Fin 2) (1 : M)))
  obtain ⟨r₁, hr₁⟩ := hφ (inr (Pi.single (1 : Fin 2) (1 : M)))
  have hm₀ : r₀ ∈ maximalIdeal R := by
    rw [← hker]
    change (φ r₀).fst = 0
    rw [hr₀]
    rfl
  have hm₁ : r₁ ∈ maximalIdeal R := by
    rw [← hker]
    change (φ r₁).fst = 0
    rw [hr₁]
    rfl
  rw [hg] at hm₀ hm₁
  obtain ⟨a₀, ha₀⟩ := Ideal.mem_span_singleton.mp hm₀
  obtain ⟨a₁, ha₁⟩ := Ideal.mem_span_singleton.mp hm₁
  have he₀ : φ (g * a₀) = inr (Pi.single (0 : Fin 2) (1 : M)) := by
    rw [← ha₀]
    exact hr₀
  have he₁ : φ (g * a₁) = inr (Pi.single (1 : Fin 2) (1 : M)) := by
    rw [← ha₁]
    exact hr₁
  have h₀₀ := congrArg (fun z : TrivSqZeroExt M (Fin 2 → M) => z.snd 0) he₀
  have h₀₁ := congrArg (fun z : TrivSqZeroExt M (Fin 2 → M) => z.snd 1) he₀
  have h₁₁ := congrArg (fun z : TrivSqZeroExt M (Fin 2 → M) => z.snd 1) he₁
  simp [map_mul, TrivSqZeroExt.snd_mul, hgzero, op_smul_eq_smul,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h₀₀ h₀₁ h₁₁
  have ha₀zero : (φ a₀).fst ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at h₀₀
    exact zero_ne_one h₀₀
  have hg₁zero : (φ g).snd 1 = 0 :=
    h₀₁.resolve_left ha₀zero
  rw [hg₁zero, mul_zero] at h₁₁
  exact zero_ne_one h₁₁

/-- The rank bound is over the local ring's actual residue field. -/
theorem cotangent_finrank_ge_two_of_surjective_fullJet
    [IsLocalRing R] [IsNoetherianRing R]
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) (hφ : Function.Surjective φ) :
    2 ≤ finrank (ResidueField R) (CotangentSpace R) := by
  have hprincipal := maximalIdeal_not_principal_of_surjective_fullJet φ hφ
  have hlarge : ¬ finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
    intro hsmall
    exact hprincipal (IsLocalRing.finrank_cotangentSpace_le_one_iff.mp hsmall)
  omega

/-- An actual surjective full jet, rather than a supplied rank certificate,
forces a normalization defect in a one-dimensional local domain. -/
theorem localNormalizationDefect_nontrivial_of_surjective_fullJet
    [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [Ring.DimensionLEOne R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) (hφ : Function.Surjective φ) :
    Nontrivial (localNormalizationDefect R F) :=
  localNormalizationDefect_nontrivial_of_cotangent_finrank_ge_two R F
    (cotangent_finrank_ge_two_of_surjective_fullJet φ hφ)

theorem localNormalizationDefect_length_pos_of_surjective_fullJet
    [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [Ring.DimensionLEOne R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) (hφ : Function.Surjective φ) :
    0 < Module.length R (localNormalizationDefect R F) :=
  localNormalizationDefect_length_pos_of_cotangent_finrank_ge_two R F
    (cotangent_finrank_ge_two_of_surjective_fullJet φ hφ)

/-- The jet's literal residue kernel is an actual maximal point ideal. -/
theorem fullJetResidueIdeal_isMaximal
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) (hφ : Function.Surjective φ) :
    (RingHom.ker (fullJetResidueMap φ)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (fullJetResidueMap φ)
    (fullJetResidueMap_surjective φ hφ)

/-- The jet extends to the localization at its actual point ideal. Nonzero
residue of every allowed denominator makes its actual jet a unit. -/
def fullJetAtActualPoint
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) (hφ : Function.Surjective φ) :
    let P := RingHom.ker (fullJetResidueMap φ)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
    Localization.AtPrime P →+* TrivSqZeroExt M (Fin 2 → M) := by
  let P := RingHom.ker (fullJetResidueMap φ)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
  apply IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) (g := φ)
  intro a
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  apply isUnit_iff_ne_zero.mpr
  exact a.property

theorem fullJetAtActualPoint_algebraMap
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) (hφ : Function.Surjective φ) (r : R) :
    let P := RingHom.ker (fullJetResidueMap φ)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
    fullJetAtActualPoint φ hφ (algebraMap R (Localization.AtPrime P) r) = φ r := by
  dsimp only [fullJetAtActualPoint]
  exact IsLocalization.lift_eq _ r

theorem fullJetAtActualPoint_surjective
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) (hφ : Function.Surjective φ) :
    Function.Surjective (fullJetAtActualPoint φ hφ) := by
  let P := RingHom.ker (fullJetResidueMap φ)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
  intro z
  obtain ⟨r, hr⟩ := hφ z
  exact ⟨algebraMap R (Localization.AtPrime P) r,
    (fullJetAtActualPoint_algebraMap φ hφ r).trans hr⟩

/-- Large cotangent rank of the actual point localization, constructed from
the original ring jet. The residue field is that of the actual local ring. -/
theorem fullJetAtActualPoint_cotangent_finrank_ge_two
    [IsNoetherianRing R]
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) (hφ : Function.Surjective φ) :
    let P := RingHom.ker (fullJetResidueMap φ)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
    2 ≤ finrank (ResidueField (Localization.AtPrime P))
      (CotangentSpace (Localization.AtPrime P)) := by
  let P := RingHom.ker (fullJetResidueMap φ)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal φ hφ).isPrime
  exact cotangent_finrank_ge_two_of_surjective_fullJet
    (fullJetAtActualPoint φ hφ) (fullJetAtActualPoint_surjective φ hφ)

end PfaffianDescent.Coray

import PfaffianDescent.CorayLocalFullJetCotangent
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Actual residue-field identification and local degree weights

An actual surjective K-algebra full jet identifies a local ring's OWN residue
field with the presented M. The actual localized jet remains a K-algebra map.
The proved local length restriction formula then supplies the genuine residue
weight for every actual finite-length module. This is a local algebra result,
not a global normalization-genus certificate.

STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open TrivSqZeroExt IsLocalRing Module

universe u v w
variable {K : Type u} [Field K]
variable {R : Type v} [CommRing R] [Algebra K R]
variable {M : Type w} [Field M] [Algebra K M]

/-- Actual full-jet residue evaluation gives an actual K-algebra equivalence
from the local ring's OWN residue field to the presented field M. -/
def localFullJetResidueAlgEquiv
    [IsLocalRing R]
    (phi : R →ₐ[K] TrivSqZeroExt M (Fin 2 → M)) (hphi : Function.Surjective phi) :
    ResidueField R ≃ₐ[K] M := by
  let eta : R →ₐ[K] M := (TrivSqZeroExt.fstHom K M (Fin 2 → M)).comp phi
  have heta : Function.Surjective eta := fullJetResidueMap_surjective phi.toRingHom hphi
  have hker : RingHom.ker eta.toRingHom = maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal eta.toRingHom heta
  exact (Ideal.quotientEquivAlgOfEq K hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective heta)

/-- The actual residue extension degree equals the presented degree. -/
theorem localFullJet_residue_finrank
    [IsLocalRing R]
    (phi : R →ₐ[K] TrivSqZeroExt M (Fin 2 → M)) (hphi : Function.Surjective phi) :
    finrank K (ResidueField R) = finrank K M :=
  (localFullJetResidueAlgEquiv phi hphi).toLinearEquiv.finrank_eq

/-- Actual finite M/K gives actual finite OWN residue extension, using the
constructed equivalence rather than a supplied residue certificate. -/
theorem localFullJet_residue_finite
    [IsLocalRing R] [FiniteDimensional K M]
    (phi : R →ₐ[K] TrivSqZeroExt M (Fin 2 → M)) (hphi : Function.Surjective phi) :
    Module.Finite K (ResidueField R) :=
  Module.Finite.equiv (localFullJetResidueAlgEquiv phi hphi).symm.toLinearEquiv

/-- The actual full jet extended to its actual residue-point localization
is an actual K-algebra homomorphism, preserving original scalar provenance. -/
def fullJetAtActualPointAlgHom
    (phi : R →ₐ[K] TrivSqZeroExt M (Fin 2 → M)) (hphi : Function.Surjective phi) :
    let P := RingHom.ker (fullJetResidueMap phi.toRingHom)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi.toRingHom hphi).isPrime
    Localization.AtPrime P →ₐ[K] TrivSqZeroExt M (Fin 2 → M) := by
  let P := RingHom.ker (fullJetResidueMap phi.toRingHom)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi.toRingHom hphi).isPrime
  exact
    { toRingHom := fullJetAtActualPoint phi.toRingHom hphi
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_apply K R (Localization.AtPrime P)]
        change fullJetAtActualPoint phi.toRingHom hphi
          (algebraMap R (Localization.AtPrime P) (algebraMap K R k)) = _
        exact (fullJetAtActualPoint_algebraMap phi.toRingHom hphi
          (algebraMap K R k)).trans (phi.commutes k) }

/-- The constructed K-algebra map is the actual existing localization lift. -/
theorem fullJetAtActualPointAlgHom_toRingHom
    (phi : R →ₐ[K] TrivSqZeroExt M (Fin 2 → M)) (hphi : Function.Surjective phi) :
    (fullJetAtActualPointAlgHom phi hphi).toRingHom =
      fullJetAtActualPoint phi.toRingHom hphi := rfl

/-- The ORIGINAL ring's actual residue-point localization has actual residue
extension degree equal to the actual presented finite point field degree. -/
theorem fullJetAtActualPoint_residue_finrank
    (phi : R →ₐ[K] TrivSqZeroExt M (Fin 2 → M)) (hphi : Function.Surjective phi) :
    let P := RingHom.ker (fullJetResidueMap phi.toRingHom)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi.toRingHom hphi).isPrime
    finrank K (ResidueField (Localization.AtPrime P)) = finrank K M :=
  localFullJet_residue_finrank (fullJetAtActualPointAlgHom phi hphi)
    (fullJetAtActualPoint_surjective phi.toRingHom hphi)

section weights

variable [IsLocalRing R]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower K R N]

/-- Actual local composition length acquires the actual residue-degree
weight on restriction to the ground field. No genus identification is used. -/
theorem localModule_ground_length_eq_residue_weight
    [Module.Finite K (ResidueField R)] :
    Module.length K N = Module.length R N * (finrank K (ResidueField R) : ENat) := by
  have hres : Module.length (ResidueField K) (ResidueField R) =
      (finrank K (ResidueField R) : ENat) := by
    rw [← Module.length_eq_of_surjective (R := ResidueField K) (M := ResidueField R)
      (residue_surjective (R := K))]
    exact Module.length_eq_finrank K (ResidueField R)
  rw [IsLocalRing.length_restrictScalars K R N, hres]

/-- Finite actual local length and finite actual residue extension force
actual finite dimension over the ground field, proved from weighted length. -/
theorem localModule_finite_over_ground_of_finiteLength
    [Module.Finite K (ResidueField R)] (hN : IsFiniteLength R N) :
    Module.Finite K N := by
  have hlen : Module.length R N ≠ ⊤ := Module.length_ne_top_iff.mpr hN
  have hground : Module.length K N ≠ ⊤ := by
    rw [localModule_ground_length_eq_residue_weight (K := K) (R := R) (N := N),
      ← ENat.natCast_toNat hlen, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  have hfinite := Module.length_ne_top_iff.mp hground
  letI : IsNoetherian K N :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  infer_instance

/-- Actual ground dimension is actual finite local length times actual
residue degree, with finite dimension constructed internally. -/
theorem localModule_ground_finrank_eq_residue_weight
    [Module.Finite K (ResidueField R)] (hN : IsFiniteLength R N) :
    finrank K N = (Module.length R N).toNat * finrank K (ResidueField R) := by
  letI : Module.Finite K N := localModule_finite_over_ground_of_finiteLength hN
  have h := localModule_ground_length_eq_residue_weight (K := K) (R := R) (N := N)
  rw [Module.length_eq_finrank K N] at h
  exact by simpa only [ENat.toNat_mul, ENat.toNat_natCast] using congrArg ENat.toNat h

/-- A literal finite-length module at the actual full-jet point contributes
its actual presented point degree, proved using the constructed OWN residue
field equivalence. No supplied residue-degree or weighted-length premise. -/
theorem localFullJet_ground_finrank_eq_presented_degree
    [FiniteDimensional K M]
    (phi : R →ₐ[K] TrivSqZeroExt M (Fin 2 → M)) (hphi : Function.Surjective phi)
    (hN : IsFiniteLength R N) :
    finrank K N = (Module.length R N).toNat * finrank K M := by
  letI : Module.Finite K (ResidueField R) := localFullJet_residue_finite phi hphi
  rw [localModule_ground_finrank_eq_residue_weight hN,
    localFullJet_residue_finrank phi hphi]

end weights
end PfaffianDescent.Coray

import PfaffianDescent.CorayNormalizationDefectFiniteLength
import PfaffianDescent.CorayActualResidueDegreeWeight
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Original-residue degree contribution of a nonregular curve local ring

SOURCE ONLY, UNVERIFIED. No Lean/Lake process was run by the author.
This local algebra replaces a need to reverse the existing full-jet criterion:
nonregularity itself forces a nonzero literal normalization defect. Its finite
length and original K dimension are derived from finite normalization and the
ring's own finite residue field. No actual scheme-stalk comparison, geometric
integrality, constant-field theorem, or selected regular point is claimed.
-/
noncomputable section
namespace PfaffianDescent.Coray

open Algebra Module IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsLocalRing R] [Ring.DimensionLEOne R]

/-- Normality of a noetherian local domain of dimension at most one would
make it a local Dedekind domain, hence principal and regular. -/
theorem not_isIntegrallyClosed_of_not_isRegularLocalRing
    (hsing : ¬ IsRegularLocalRing R) : ¬ IsIntegrallyClosed R := by
  intro hnormal
  letI : IsIntegrallyClosed R := hnormal
  letI : IsDedekindDomain R :=
    (isDedekindDomain_iff R (FractionRing R)).mpr
      ⟨inferInstance, inferInstance, inferInstance,
        fun {_} => (isIntegrallyClosed_iff (FractionRing R)).mp hnormal⟩
  exact hsing (inferInstance : IsRegularLocalRing R)

variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

/-- A nonregular original local ring has a nonzero class in its OWN literal
normalization quotient, independently of how its singularity was detected. -/
theorem localNormalizationDefect_nontrivial_of_not_isRegularLocalRing
    (hsing : ¬ IsRegularLocalRing R) :
    Nontrivial (localNormalizationDefect R F) := by
  classical
  have hnormal := not_isIntegrallyClosed_of_not_isRegularLocalRing R hsing
  have hout : ∃ x : F, IsIntegral R x ∧ ¬ ∃ r : R, algebraMap R F r = x := by
    by_contra hnone
    apply hnormal
    apply (isIntegrallyClosed_iff F).mpr
    intro x hx
    by_contra hnot
    exact hnone ⟨x, hx, hnot⟩
  obtain ⟨x, hx, houtside⟩ := hout
  let b : integralClosure R F := ⟨x, hx⟩
  change Nontrivial ((integralClosure R F) ⧸
    LinearMap.range (Algebra.linearMap R (integralClosure R F)))
  apply Submodule.Quotient.nontrivial_iff.mpr
  intro hrange
  have hb : b ∈ LinearMap.range
      (Algebra.linearMap R (integralClosure R F)) := by
    rw [hrange]
    exact Submodule.mem_top
  obtain ⟨r, hr⟩ := hb
  apply houtside
  refine ⟨r, ?_⟩
  have hval := congrArg (fun z : integralClosure R F => (z : F)) hr
  change algebraMap R F r = x at hval
  exact hval

/-- A nonregular curve local ring contributes at least the full degree of
its OWN residue field. This represents every conjugate over the original K
in one ground-field calculation, without passing to a splitting field. -/
theorem localNormalizationDefect_original_ground_degree_lower_bound_of_nonregular
    (K : Type*) [Field K] [Algebra K R] [Algebra K F] [IsScalarTower K R F]
    [Module.Finite K (ResidueField R)] [Module.Finite R (integralClosure R F)]
    (hsing : ¬ IsRegularLocalRing R) :
    Module.Finite K (localNormalizationDefect R F) ∧
      finrank K (localNormalizationDefect R F) =
        (Module.length R (localNormalizationDefect R F)).toNat *
          finrank K (ResidueField R) ∧
      finrank K (ResidueField R) ≤ finrank K (localNormalizationDefect R F) := by
  letI := localNormalizationDefect_nontrivial_of_not_isRegularLocalRing R F hsing
  have hlength := localNormalizationDefect_isFiniteLength_of_finiteNormalization R F
  have hneTop := Module.length_ne_top_iff.mpr hlength
  have hpos : 0 < Module.length R (localNormalizationDefect R F) := Module.length_pos
  have hlower : 1 ≤ (Module.length R (localNormalizationDefect R F)).toNat :=
    ENat.toNat_pos (ne_of_gt hpos) hneTop
  have hweight := localModule_ground_finrank_eq_residue_weight
    (K := K) (R := R) (N := localNormalizationDefect R F) hlength
  refine ⟨localModule_finite_over_ground_of_finiteLength hlength, hweight, ?_⟩
  calc
    finrank K (ResidueField R) = 1 * finrank K (ResidueField R) := (one_mul _).symm
    _ ≤ (Module.length R (localNormalizationDefect R F)).toNat *
        finrank K (ResidueField R) := Nat.mul_le_mul_right _ hlower
    _ = finrank K (localNormalizationDefect R F) := hweight.symm

end PfaffianDescent.Coray

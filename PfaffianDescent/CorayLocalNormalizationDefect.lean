import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Length
import Lean.Elab.Tactic.Omega

/-!
# A local normalization defect forced by a double point

This is a local prerequisite for Coray's boundary-degree curve construction.
A one-dimensional noetherian local domain whose cotangent space has dimension
at least two is not integrally closed. We construct an actual integral fraction
outside the ring and a nonzero class in the actual normalization quotient.

The geometric bridge from a selected surface jet to this local cotangent rank,
finiteness of curve normalization, and the global genus comparison are separate
missing steps. No genus or divisor-effectivity premise is introduced here.

STATUS: source draft, UNVERIFIED. Root owns all compiler checks.
-/

namespace PfaffianDescent.Coray

open Module IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsLocalRing R] [Ring.DimensionLEOne R]

/-- A singular one-dimensional local domain is not integrally closed. -/
theorem not_isIntegrallyClosed_of_cotangent_finrank_ge_two
    (h : 2 ≤ finrank (ResidueField R) (CotangentSpace R)) :
    ¬ IsIntegrallyClosed R := by
  intro hnormal
  letI : IsIntegrallyClosed R := hnormal
  letI : IsDedekindDomain R :=
    (isDedekindDomain_iff R (FractionRing R)).mpr
      ⟨inferInstance, inferInstance, inferInstance,
        fun {_} => (isIntegrallyClosed_iff (FractionRing R)).mp hnormal⟩
  have hprincipal := maximalIdeal_isPrincipal_of_isDedekindDomain R
  have hsmall : finrank (ResidueField R) (CotangentSpace R) ≤ 1 :=
    IsLocalRing.finrank_cotangentSpace_le_one_iff.mpr hprincipal
  omega

variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

/-- The failure of normality gives a genuine integral element of the fraction
field which does not come from the local ring. -/
theorem exists_integral_fraction_outside_of_cotangent_finrank_ge_two
    (h : 2 ≤ finrank (ResidueField R) (CotangentSpace R)) :
    ∃ x : F, IsIntegral R x ∧ ¬ ∃ r : R, algebraMap R F r = x := by
  classical
  have hnormal := not_isIntegrallyClosed_of_cotangent_finrank_ge_two R h
  by_contra hnone
  apply hnormal
  apply (isIntegrallyClosed_iff F).mpr
  intro x hx
  by_contra houtside
  exact hnone ⟨x, hx, houtside⟩

/-- The literal normalization module modulo the image of the original ring. -/
noncomputable abbrev localNormalizationDefect : Type _ :=
  (integralClosure R F) ⧸
    LinearMap.range (Algebra.linearMap R (integralClosure R F))

/-- A double point contributes a nonzero class to the literal normalization
quotient. No finite-length or global-genus claim is hidden in this statement. -/
theorem localNormalizationDefect_nontrivial_of_cotangent_finrank_ge_two
    (h : 2 ≤ finrank (ResidueField R) (CotangentSpace R)) :
    Nontrivial (localNormalizationDefect R F) := by
  classical
  obtain ⟨x, hx, houtside⟩ :=
    exists_integral_fraction_outside_of_cotangent_finrank_ge_two R F h
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

/-- The literal normalization defect has positive module length. The length
is an extended natural number: finiteness is deliberately not asserted. -/
theorem localNormalizationDefect_length_pos_of_cotangent_finrank_ge_two
    (h : 2 ≤ finrank (ResidueField R) (CotangentSpace R)) :
    0 < Module.length R (localNormalizationDefect R F) := by
  letI := localNormalizationDefect_nontrivial_of_cotangent_finrank_ge_two R F h
  exact Module.length_pos

end PfaffianDescent.Coray

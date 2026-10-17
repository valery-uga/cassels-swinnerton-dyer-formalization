import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PfaffianDescent
open Module
section
variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- Alternating two-forms, equivalently linear forms on the second exterior power. -/
abbrev AlternatingTwoForms := V [⋀^Fin 2]→ₗ[R] R

/-- Restriction of alternating forms to an actual submodule. -/
def alternatingRestriction (W : Submodule R V) :
    AlternatingTwoForms R V →ₗ[R] AlternatingTwoForms R W where
  toFun B := B.compLinearMap W.subtype
  map_add' B C := AlternatingMap.add_compLinearMap B C W.subtype
  map_smul' c B := by ext v; rfl

/-- A splitting of a submodule inclusion extends every alternating form. -/
theorem alternatingRestriction_surjective_of_retraction (W : Submodule R V)
    (p : V →ₗ[R] W) (hp : p.comp W.subtype = LinearMap.id) :
    Function.Surjective (alternatingRestriction R V W) := by
  intro B
  refine ⟨B.compLinearMap p, ?_⟩
  change (B.compLinearMap p).compLinearMap W.subtype = B
  rw [AlternatingMap.compLinearMap_assoc, hp, AlternatingMap.compLinearMap_id]

end
section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Restriction of alternating forms to a vector subspace is surjective. -/
theorem alternatingRestriction_surjective (W : Submodule K V) :
    Function.Surjective (alternatingRestriction K V W) := by
  obtain ⟨p, hp⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  exact alternatingRestriction_surjective_of_retraction K V W p hp

variable [FiniteDimensional K V]

instance alternatingTwoForms_finite : Module.Finite K (AlternatingTwoForms K V) :=
  Module.Finite.equiv (exteriorPower.alternatingMapLinearEquiv
    (R := K) (M := V) (N := K) (n := 2)).symm

/-- The dimension of alternating forms is the binomial coefficient. -/
theorem alternatingTwoForms_finrank :
    finrank K (AlternatingTwoForms K V) = (finrank K V).choose 2 := by
  calc
    _ = finrank K (Module.Dual K (⋀[K]^2 V)) :=
      (exteriorPower.alternatingMapLinearEquiv (R := K) (M := V) (N := K) (n := 2)).finrank_eq
    _ = finrank K (⋀[K]^2 V) := Subspace.dual_finrank_eq
    _ = (finrank K V).choose 2 := exteriorPower.finrank_eq (M := V) K 2

/-- Restriction from six dimensions to three has a twelve-dimensional kernel. -/
theorem alternatingRestriction_kernel_twelve (W : Submodule K V)
    (hV : finrank K V = 6) (hW : finrank K W = 3) :
    finrank K (LinearMap.ker (alternatingRestriction K V W)) = 12 := by
  have h := (alternatingRestriction K V W).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (alternatingRestriction_surjective W), finrank_top,
    alternatingTwoForms_finrank, alternatingTwoForms_finrank, hV, hW] at h
  norm_num [Nat.choose] at h
  omega

/-- The restriction map on ordered triples of alternating forms. -/
def tripleAlternatingRestriction (W : Submodule K V) :
    (Fin 3 → AlternatingTwoForms K V) →ₗ[K] (Fin 3 → AlternatingTwoForms K W) :=
  LinearMap.pi (fun i => (alternatingRestriction K V W).comp (LinearMap.proj i))

omit [FiniteDimensional K V] in
lemma tripleAlternatingRestriction_surjective (W : Submodule K V) :
    Function.Surjective (tripleAlternatingRestriction W) := by
  intro B
  choose C hC using fun i => alternatingRestriction_surjective W (B i)
  exact ⟨C, funext hC⟩

/-- The space of triples vanishing on a fixed three-space has dimension
thirty-six; this is the fiber dimension of the incidence bundle. -/
theorem tripleAlternatingRestriction_kernel_thirtysix (W : Submodule K V)
    (hV : finrank K V = 6) (hW : finrank K W = 3) :
    finrank K (LinearMap.ker (tripleAlternatingRestriction W)) = 36 := by
  have h := (tripleAlternatingRestriction W).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (tripleAlternatingRestriction_surjective W), finrank_top,
    Module.finrank_pi_fintype, Module.finrank_pi_fintype] at h
  simp only [alternatingTwoForms_finrank, hV, hW, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  norm_num [Nat.choose] at h
  omega

end
end PfaffianDescent

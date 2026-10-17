import AllCharacteristics.MonicRootCompletion
import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
# Specifying a residue field by a surjective homomorphism

A surjection from a local ring onto a field identifies that field with the
intrinsic residue field. The identification is compatible with the original
homomorphism, so polynomial reductions and their irreducibility can be
transported without changing any coefficient maps.
-/

open IsLocalRing Polynomial
namespace AllCharacteristics
universe u v

/-- A surjective field-valued homomorphism presents the actual residue field. -/
noncomputable def residueEquivOfSurjective
    {R : Type u} {k : Type v} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b) : ResidueField R ≃+* k :=
  (Ideal.quotEquivOfEq (IsLocalRing.ker_eq_maximalIdeal b hb).symm).trans
    (RingHom.quotientKerEquivOfSurjective hb)

/-- The residue-field identification recovers the prescribed surjection. -/
theorem residueEquivOfSurjective_residue
    {R : Type u} {k : Type v} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b) (r : R) :
    residueEquivOfSurjective b hb (residue R r) = b r := by
  exact (congrArg (RingHom.quotientKerEquivOfSurjective hb)
    (Ideal.quotEquivOfEq_mk (IsLocalRing.ker_eq_maximalIdeal b hb).symm r)).trans
    (RingHom.quotientKerEquivOfSurjective_apply_mk hb r)

/-- Polynomial reduction through the intrinsic residue field agrees with
reduction through its prescribed presentation. -/
theorem polynomial_map_residueEquivOfSurjective
    {R : Type u} {k : Type v} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b) (q : R[X]) :
    (q.map (residue R)).map (residueEquivOfSurjective b hb).toRingHom = q.map b := by
  rw [Polynomial.map_map]
  exact congrArg (fun f : R →+* k ↦ q.map f)
    (RingHom.ext (fun r ↦ residueEquivOfSurjective_residue b hb r))

/-- Irreducibility is independent of the chosen presentation of the residue
field, including for inseparable polynomials. -/
theorem irreducible_residue_of_surjective_reduction
    {R : Type u} {k : Type v} [CommRing R] [IsLocalRing R] [Field k]
    (b : R →+* k) (hb : Function.Surjective b) (q : R[X])
    (hi : Irreducible (q.map b)) : Irreducible (q.map (residue R)) := by
  apply (MulEquiv.irreducible_iff (Polynomial.mapEquiv
    (residueEquivOfSurjective b hb))).mp
  change Irreducible ((q.map (residue R)).map (residueEquivOfSurjective b hb).toRingHom)
  rw [polynomial_map_residueEquivOfSurjective b hb q]
  exact hi

end AllCharacteristics

import PfaffianDescent.CorayPlaneSectionGradedQuotient
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-! The literal surface coordinate restriction and the elementary regular
hyperplane kernel cut. No dimension or geometric outcome is an input. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Ordinary regularity on J forces the hyperplane coefficient back into J. -/
theorem regularHyperplane_pairIdeal_mem_iff
    {A : Type u} [CommRing A] (J : Ideal A) (f H : A) (hf : f ∈ J)
    (hH : ∀ b : A, H * b ∈ J → b ∈ J) (q : A) (hq : q ∈ J) :
    q ∈ Ideal.span ({f, H} : Set A) ↔
      ∃ a b : A, b ∈ J ∧ a * f + H * b = q := by
  constructor
  · intro hpair
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hpair
    have hHb : H * b ∈ J := by
      have hsub := J.sub_mem hq (J.mul_mem_left a hf)
      have heq : q - a * f = H * b := by rw [← hab]; ring
      rwa [heq] at hsub
    exact ⟨a, b, hH b hHb, by simpa only [mul_comm b H] using hab⟩
  · rintro ⟨a, b, _hb, hab⟩
    exact Ideal.mem_span_pair.mpr ⟨a, b, by simpa only [mul_comm b H] using hab⟩

/-- The same polynomial substitution respects the actual surface equation. -/
theorem surfacePlaneCoordinateRestriction_ideal_le
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d) :
    (equationIdeal p hp).toIdeal ≤
      (equationIdeal (planeHyperplaneRestrictionHom t p)
        (planeHyperplaneRestrictionHom_homogeneous t p hp)).toIdeal.comap
          (planeHyperplaneRestrictionHom t).toRingHom := by
  change Ideal.span ({p} : Set (MvPolynomial (Fin 4) R)) ≤ _
  apply Ideal.span_le.mpr
  intro q hq
  obtain rfl := Set.mem_singleton_iff.mp hq
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Restriction of the original SURFACE coordinate quotient, rather than the
pair quotient, to the same literal plane cubic coordinate quotient. -/
def surfacePlaneCoordinateRestriction
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d) :
    CoordinateRing (equationIdeal p hp) →ₐ[R]
      CoordinateRing (equationIdeal (planeHyperplaneRestrictionHom t p)
        (planeHyperplaneRestrictionHom_homogeneous t p hp)) :=
  { PfaffianDescent.polynomialQuotientMap _ _ (planeHyperplaneRestrictionHom t)
      (surfacePlaneCoordinateRestriction_ideal_le t p hp) with
    commutes' := PfaffianDescent.polynomialQuotientMap_base _ _
      (planeHyperplaneRestrictionHom t) (surfacePlaneCoordinateRestriction_ideal_le t p hp) }

@[simp] theorem surfacePlaneCoordinateRestriction_mk
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d)
    (q : MvPolynomial (Fin 4) R) :
    surfacePlaneCoordinateRestriction t p hp (Ideal.Quotient.mk (equationIdeal p hp).toIdeal q) =
      Ideal.Quotient.mk (equationIdeal (planeHyperplaneRestrictionHom t p)
        (planeHyperplaneRestrictionHom_homogeneous t p hp)).toIdeal
          (planeHyperplaneRestrictionHom t q) :=
  PfaffianDescent.polynomialQuotientMap_mk _ _ (planeHyperplaneRestrictionHom t)
    (surfacePlaneCoordinateRestriction_ideal_le t p hp) q

/-- The kernel on polynomial representatives is the genuine pair (p,H). -/
theorem surfacePlaneCoordinateRestriction_mk_eq_zero_iff
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d)
    (q : MvPolynomial (Fin 4) R) :
    surfacePlaneCoordinateRestriction t p hp (Ideal.Quotient.mk (equationIdeal p hp).toIdeal q) = 0 ↔
      q ∈ Ideal.span ({p, planeHyperplaneRelation t} : Set (MvPolynomial (Fin 4) R)) := by
  rw [surfacePlaneCoordinateRestriction_mk]
  change q ∈ RingHom.ker
    ((Ideal.Quotient.mk (equationIdeal (planeHyperplaneRestrictionHom t p)
      (planeHyperplaneRestrictionHom_homogeneous t p hp)).toIdeal).comp
        (planeHyperplaneRestrictionHom t).toRingHom) ↔ _
  rw [planeSection_restriction_to_quotient_ker t p hp, planeSectionHomogeneousIdeal_toIdeal t p hp]

/-- The same hyperplane class maps to zero in the literal plane quotient. -/
theorem surfacePlaneCoordinateRestriction_hyperplane
    (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d) :
    surfacePlaneCoordinateRestriction t p hp
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal (planeHyperplaneRelation t)) = 0 := by
  rw [surfacePlaneCoordinateRestriction_mk, planeHyperplaneRestrictionHom_relation, map_zero]

end PfaffianDescent.Coray

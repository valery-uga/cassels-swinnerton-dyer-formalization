import PfaffianDescent.CorayPlaneRestrictionKernel
import PfaffianDescent.PolynomialProjectiveMap

/-! SOURCE ONLY / UNVERIFIED151. Explicit forward/inverse ACTUAL homogeneous
coordinate quotient maps for (p,H) and the SAME restricted polynomial. Both
maps preserve the real quotient gradings; no quotient/Proj comparison premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual four-variable homogeneous ideal (p,H), without saturation or
replacement by any component. -/
def planeSectionHomogeneousIdeal (t : Fin 3 → R)
    (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) R) :=
  equationIdeal p hp ⊔ equationIdeal (planeHyperplaneRelation t) (planeHyperplaneRelation_homogeneous t)

theorem planeSectionHomogeneousIdeal_toIdeal (t : Fin 3 → R)
    (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d) :
    (planeSectionHomogeneousIdeal t p hp).toIdeal = Ideal.span {p, planeHyperplaneRelation t} := by
  rw [planeSectionHomogeneousIdeal, HomogeneousIdeal.toIdeal_sup]
  change Ideal.span {p} ⊔ Ideal.span {planeHyperplaneRelation t} = _
  rw [← Ideal.span_union]
  congr 1

variable (t : Fin 3 → R) (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d)
local notation "I" => planeSectionHomogeneousIdeal t p hp
local notation "J" => equationIdeal (planeHyperplaneRestrictionHom t p)
  (planeHyperplaneRestrictionHom_homogeneous t p hp)

/-- The literal hyperplane kernel ideal is contained in the actual pair. -/
theorem planeSection_relation_span_le :
    Ideal.span ({planeHyperplaneRelation t} : Set (MvPolynomial (Fin 4) R)) ≤ (I).toIdeal := by
  rw [planeSectionHomogeneousIdeal_toIdeal]
  apply Ideal.span_mono
  intro q hq
  exact Set.mem_insert_of_mem _ hq

theorem planeSection_polynomial_difference_mem (q : MvPolynomial (Fin 4) R) :
    q - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t q) ∈ (I).toIdeal :=
  planeSection_relation_span_le t p hp (planeRestriction_polynomial_difference_mem t q)

/-- Actual restriction respects both defining equations p,H. -/
theorem planeSection_restriction_ideal_le :
    (I).toIdeal ≤ (J).toIdeal.comap (planeHyperplaneRestrictionHom t).toRingHom := by
  rw [planeSectionHomogeneousIdeal_toIdeal]
  apply Ideal.span_le.mpr
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · exact Ideal.subset_span (Set.mem_singleton _)
  · change planeHyperplaneRestrictionHom t (planeHyperplaneRelation t) ∈ (J).toIdeal
    rw [planeHyperplaneRestrictionHom_relation]
    exact Ideal.zero_mem _

/-- Retained inclusion respects the restricted equation, because p differs
from its retained/restricted lift by the actual hyperplane ideal. -/
theorem planeSection_inclusion_ideal_le :
    (J).toIdeal ≤ (I).toIdeal.comap (planeRetainedInclusionHom (R := R)).toRingHom := by
  change Ideal.span {planeHyperplaneRestrictionHom t p} ≤ _
  apply Ideal.span_le.mpr
  intro q hq
  obtain rfl := Set.mem_singleton_iff.mp hq
  change planeRetainedInclusionHom (planeHyperplaneRestrictionHom t p) ∈ (I).toIdeal
  have hpmem : p ∈ (I).toIdeal := by
    rw [planeSectionHomogeneousIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hdiff := planeSection_polynomial_difference_mem t p hp p
  have hsub := (I).toIdeal.sub_mem hpmem hdiff
  have heq : p - (p - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t p)) =
      planeRetainedInclusionHom (planeHyperplaneRestrictionHom t p) := by ring
  rwa [heq] at hsub

/-- The literal quotient substitution as a coefficient algebra homomorphism. -/
def planeSectionQuotientRestriction : CoordinateRing I →ₐ[R] CoordinateRing J :=
  { PfaffianDescent.polynomialQuotientMap I J (planeHyperplaneRestrictionHom t)
      (planeSection_restriction_ideal_le t p hp) with
    commutes' := PfaffianDescent.polynomialQuotientMap_base I J
      (planeHyperplaneRestrictionHom t) (planeSection_restriction_ideal_le t p hp) }

/-- The inverse quotient map is literal retained inclusion. -/
def planeSectionQuotientInclusion : CoordinateRing J →ₐ[R] CoordinateRing I :=
  { PfaffianDescent.polynomialQuotientMap J I (planeRetainedInclusionHom (R := R))
      (planeSection_inclusion_ideal_le t p hp) with
    commutes' := PfaffianDescent.polynomialQuotientMap_base J I
      (planeRetainedInclusionHom (R := R)) (planeSection_inclusion_ideal_le t p hp) }

@[simp] theorem planeSectionQuotientRestriction_mk (q : MvPolynomial (Fin 4) R) :
    planeSectionQuotientRestriction t p hp (Ideal.Quotient.mk (I).toIdeal q) =
      Ideal.Quotient.mk (J).toIdeal (planeHyperplaneRestrictionHom t q) :=
  PfaffianDescent.polynomialQuotientMap_mk I J (planeHyperplaneRestrictionHom t)
    (planeSection_restriction_ideal_le t p hp) q

@[simp] theorem planeSectionQuotientInclusion_mk (q : MvPolynomial (Fin 3) R) :
    planeSectionQuotientInclusion t p hp (Ideal.Quotient.mk (J).toIdeal q) =
      Ideal.Quotient.mk (I).toIdeal (planeRetainedInclusionHom q) :=
  PfaffianDescent.polynomialQuotientMap_mk J I (planeRetainedInclusionHom (R := R))
    (planeSection_inclusion_ideal_le t p hp) q

/-- Forward after inverse is identity on the ACTUAL restricted quotient. -/
theorem planeSectionQuotientRestriction_comp_inclusion :
    (planeSectionQuotientRestriction t p hp).comp (planeSectionQuotientInclusion t p hp) =
      AlgHom.id R (CoordinateRing J) := by
  apply AlgHom.ext
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change planeSectionQuotientRestriction t p hp
    (planeSectionQuotientInclusion t p hp (Ideal.Quotient.mk (J).toIdeal q)) = Ideal.Quotient.mk (J).toIdeal q
  rw [planeSectionQuotientInclusion_mk, planeSectionQuotientRestriction_mk]
  exact congrArg (Ideal.Quotient.mk (J).toIdeal)
    (AlgHom.congr_fun (planeHyperplaneRestrictionHom_comp_inclusion t) q)

/-- Inverse after forward is identity on the ACTUAL (p,H) quotient; the
polynomial congruence, not an assumed equivalence, constructs this identity. -/
theorem planeSectionQuotientInclusion_comp_restriction :
    (planeSectionQuotientInclusion t p hp).comp (planeSectionQuotientRestriction t p hp) =
      AlgHom.id R (CoordinateRing I) := by
  apply AlgHom.ext
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change planeSectionQuotientInclusion t p hp
    (planeSectionQuotientRestriction t p hp (Ideal.Quotient.mk (I).toIdeal q)) = Ideal.Quotient.mk (I).toIdeal q
  rw [planeSectionQuotientRestriction_mk, planeSectionQuotientInclusion_mk]
  apply Eq.symm
  exact Ideal.Quotient.eq.mpr (planeSection_polynomial_difference_mem t p hp q)

/-- Actual coordinate algebra equivalence between the pair ideal and the
literal plane equation, with both maps explicitly constructed. -/
def planeSectionCoordinateAlgEquiv : CoordinateRing I ≃ₐ[R] CoordinateRing J :=
  AlgEquiv.ofAlgHom (planeSectionQuotientRestriction t p hp) (planeSectionQuotientInclusion t p hp)
    (planeSectionQuotientRestriction_comp_inclusion t p hp)
    (planeSectionQuotientInclusion_comp_restriction t p hp)

/-- The composite polynomial restriction to the ACTUAL restricted quotient
has exactly the literal pair ideal as its kernel, in every degree at once. -/
theorem planeSection_restriction_to_quotient_ker :
    RingHom.ker ((Ideal.Quotient.mk (J).toIdeal).comp
      (planeHyperplaneRestrictionHom t).toRingHom) = (I).toIdeal := by
  apply le_antisymm
  · intro q hq
    have hz : planeSectionQuotientRestriction t p hp (Ideal.Quotient.mk (I).toIdeal q) = 0 := hq
    have hb := congrArg (planeSectionQuotientInclusion t p hp) hz
    rw [map_zero] at hb
    have hid := AlgHom.congr_fun (planeSectionQuotientInclusion_comp_restriction t p hp)
      (Ideal.Quotient.mk (I).toIdeal q)
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hid.symm.trans hb)
  · intro q hq
    have hmem := planeSection_restriction_ideal_le t p hp hq
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

/-- The forward equivalence preserves the real quotient grading. -/
def planeSectionGradedRestriction : grading I →+*ᵍ grading J :=
  PfaffianDescent.polynomialQuotientGradingMap I J (planeHyperplaneRestrictionHom t)
    (planeSection_restriction_ideal_le t p hp)
    (fun _ q hq => planeHyperplaneRestrictionHom_homogeneous t q hq)

/-- The literal inverse also preserves the real quotient grading. -/
def planeSectionGradedInclusion : grading J →+*ᵍ grading I :=
  PfaffianDescent.polynomialQuotientGradingMap J I (planeRetainedInclusionHom (R := R))
    (planeSection_inclusion_ideal_le t p hp)
    (fun _ q hq => planeRetainedInclusionHom_homogeneous q hq)

theorem planeSectionGradedRestriction_comp_inclusion :
    (planeSectionGradedRestriction t p hp).comp (planeSectionGradedInclusion t p hp) =
      GradedRingHom.id (grading J) := by
  apply GradedRingHom.ext
  intro x
  exact AlgHom.congr_fun (planeSectionQuotientRestriction_comp_inclusion t p hp) x

theorem planeSectionGradedInclusion_comp_restriction :
    (planeSectionGradedInclusion t p hp).comp (planeSectionGradedRestriction t p hp) =
      GradedRingHom.id (grading I) := by
  apply GradedRingHom.ext
  intro x
  exact AlgHom.congr_fun (planeSectionQuotientInclusion_comp_restriction t p hp) x

theorem planeSectionGradedRestriction_surjective :
    Function.Surjective (planeSectionGradedRestriction t p hp) := by
  intro y
  exact ⟨planeSectionGradedInclusion t p hp y,
    DFunLike.congr_fun (planeSectionGradedRestriction_comp_inclusion t p hp) y⟩

theorem planeSectionGradedInclusion_surjective :
    Function.Surjective (planeSectionGradedInclusion t p hp) := by
  intro x
  exact ⟨planeSectionGradedRestriction t p hp x,
    DFunLike.congr_fun (planeSectionGradedInclusion_comp_restriction t p hp) x⟩

end PfaffianDescent.Coray


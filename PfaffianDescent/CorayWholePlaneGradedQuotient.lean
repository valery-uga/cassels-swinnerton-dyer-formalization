import PfaffianDescent.CorayPlaneRestrictionKernel
import Mathlib.RingTheory.Ideal.Quotient.Operations
import PfaffianDescent.PolynomialProjectiveMap
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/- SOURCE ONLY: native accepted imports; uncompiled. -/

/-! SOURCE ONLY / UNVERIFIED155. Literal split elimination for an ARBITRARY
whole homogeneous ideal containing the actual hyperplane. Its whole ideal map
is homogeneous natively, and actual inverse quotient maps preserve gradings.
No saturation, reduced ideal, prime component or quotient comparison premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

def planeRestrictionPolynomialGradedHom (t : Fin 3 → R) :
    homogeneousSubmodule (Fin 4) R →+*ᵍ homogeneousSubmodule (Fin 3) R where
  __ := (planeHyperplaneRestrictionHom t).toRingHom
  map_mem := by intro d q hq; exact planeHyperplaneRestrictionHom_homogeneous t q hq

/-- The ENTIRE native homogeneous ideal image, retaining all thickness. -/
def wholePlaneRestrictionIdeal (t : Fin 3 → R)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R)) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 3) R) :=
  I.map (planeRestrictionPolynomialGradedHom t)

theorem wholePlaneRestrictionIdeal_toIdeal (t : Fin 3 → R)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R)) :
    (wholePlaneRestrictionIdeal t I).toIdeal =
      I.toIdeal.map (planeHyperplaneRestrictionHom t).toRingHom := rfl

variable (t : Fin 3 → R) (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hH : Ideal.span ({planeHyperplaneRelation t} : Set (MvPolynomial (Fin 4) R)) ≤ I.toIdeal)
local notation "D" => wholePlaneRestrictionIdeal t I

include hH in
theorem wholePlane_polynomial_difference_mem (q : MvPolynomial (Fin 4) R) :
    q - planeRetainedInclusionHom (planeHyperplaneRestrictionHom t q) ∈ I.toIdeal :=
  hH (planeRestriction_polynomial_difference_mem t q)

theorem wholePlane_restriction_ideal_le :
    I.toIdeal ≤ (D).toIdeal.comap (planeHyperplaneRestrictionHom t).toRingHom := by
  intro q hq
  exact Ideal.mem_map_of_mem _ hq

/- Actual ideal image membership lifts through the surjective literal split
restriction; the congruence puts its retained-variable lift back in whole I. -/
include hH in
theorem wholePlane_inclusion_ideal_le :
    (D).toIdeal ≤ I.toIdeal.comap (planeRetainedInclusionHom (R := R)).toRingHom := by
  intro q hq
  rw [wholePlaneRestrictionIdeal_toIdeal] at hq
  obtain ⟨p, hp, hpq⟩ :=
    (Ideal.mem_map_iff_of_surjective (planeHyperplaneRestrictionHom t).toRingHom
      (planeHyperplaneRestrictionHom_surjective t)).mp hq
  change planeHyperplaneRestrictionHom t p = q at hpq
  change planeRetainedInclusionHom q ∈ I.toIdeal
  rw [← hpq]
  have hdiff := wholePlane_polynomial_difference_mem t I hH p
  have hsub := I.toIdeal.sub_mem hp hdiff
  simpa only [sub_sub_cancel] using hsub

def wholePlaneQuotientRestriction : CoordinateRing I →ₐ[R] CoordinateRing D :=
  { PfaffianDescent.polynomialQuotientMap I D (planeHyperplaneRestrictionHom t)
      (wholePlane_restriction_ideal_le t I) with
    commutes' := PfaffianDescent.polynomialQuotientMap_base I D
      (planeHyperplaneRestrictionHom t) (wholePlane_restriction_ideal_le t I) }

def wholePlaneQuotientInclusion : CoordinateRing D →ₐ[R] CoordinateRing I :=
  { PfaffianDescent.polynomialQuotientMap D I (planeRetainedInclusionHom (R := R))
      (wholePlane_inclusion_ideal_le t I hH) with
    commutes' := PfaffianDescent.polynomialQuotientMap_base D I
      (planeRetainedInclusionHom (R := R)) (wholePlane_inclusion_ideal_le t I hH) }

@[simp] theorem wholePlaneQuotientRestriction_mk (q : MvPolynomial (Fin 4) R) :
    wholePlaneQuotientRestriction t I (Ideal.Quotient.mk I.toIdeal q) =
      Ideal.Quotient.mk (D).toIdeal (planeHyperplaneRestrictionHom t q) :=
  PfaffianDescent.polynomialQuotientMap_mk I D (planeHyperplaneRestrictionHom t)
    (wholePlane_restriction_ideal_le t I) q

@[simp] theorem wholePlaneQuotientInclusion_mk (q : MvPolynomial (Fin 3) R) :
    wholePlaneQuotientInclusion t I hH (Ideal.Quotient.mk (D).toIdeal q) =
      Ideal.Quotient.mk I.toIdeal (planeRetainedInclusionHom q) :=
  PfaffianDescent.polynomialQuotientMap_mk D I (planeRetainedInclusionHom (R := R))
    (wholePlane_inclusion_ideal_le t I hH) q

theorem wholePlaneQuotientRestriction_comp_inclusion :
    (wholePlaneQuotientRestriction t I).comp (wholePlaneQuotientInclusion t I hH) =
      AlgHom.id R (CoordinateRing D) := by
  apply AlgHom.ext
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change wholePlaneQuotientRestriction t I
    (wholePlaneQuotientInclusion t I hH (Ideal.Quotient.mk (D).toIdeal q)) = Ideal.Quotient.mk (D).toIdeal q
  rw [wholePlaneQuotientInclusion_mk, wholePlaneQuotientRestriction_mk]
  exact congrArg (Ideal.Quotient.mk (D).toIdeal)
    (AlgHom.congr_fun (planeHyperplaneRestrictionHom_comp_inclusion t) q)

theorem wholePlaneQuotientInclusion_comp_restriction :
    (wholePlaneQuotientInclusion t I hH).comp (wholePlaneQuotientRestriction t I) =
      AlgHom.id R (CoordinateRing I) := by
  apply AlgHom.ext
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change wholePlaneQuotientInclusion t I hH
    (wholePlaneQuotientRestriction t I (Ideal.Quotient.mk I.toIdeal q)) = Ideal.Quotient.mk I.toIdeal q
  rw [wholePlaneQuotientRestriction_mk, wholePlaneQuotientInclusion_mk]
  exact (Ideal.Quotient.eq.mpr (wholePlane_polynomial_difference_mem t I hH q)).symm

def wholePlaneCoordinateAlgEquiv : CoordinateRing I ≃ₐ[R] CoordinateRing D :=
  AlgEquiv.ofAlgHom (wholePlaneQuotientRestriction t I) (wholePlaneQuotientInclusion t I hH)
    (wholePlaneQuotientRestriction_comp_inclusion t I hH)
    (wholePlaneQuotientInclusion_comp_restriction t I hH)

def wholePlaneGradedRestriction : grading I →+*ᵍ grading D :=
  PfaffianDescent.polynomialQuotientGradingMap I D (planeHyperplaneRestrictionHom t)
    (wholePlane_restriction_ideal_le t I)
    (fun _ q hq => planeHyperplaneRestrictionHom_homogeneous t q hq)

def wholePlaneGradedInclusion : grading D →+*ᵍ grading I :=
  PfaffianDescent.polynomialQuotientGradingMap D I (planeRetainedInclusionHom (R := R))
    (wholePlane_inclusion_ideal_le t I hH)
    (fun _ q hq => planeRetainedInclusionHom_homogeneous q hq)

theorem wholePlaneGradedRestriction_comp_inclusion :
    (wholePlaneGradedRestriction t I).comp (wholePlaneGradedInclusion t I hH) =
      GradedRingHom.id (grading D) := by
  apply GradedRingHom.ext
  intro x
  exact AlgHom.congr_fun (wholePlaneQuotientRestriction_comp_inclusion t I hH) x

theorem wholePlaneGradedInclusion_comp_restriction :
    (wholePlaneGradedInclusion t I hH).comp (wholePlaneGradedRestriction t I) =
      GradedRingHom.id (grading I) := by
  apply GradedRingHom.ext
  intro x
  exact AlgHom.congr_fun (wholePlaneQuotientInclusion_comp_restriction t I hH) x

include hH in
theorem wholePlaneGradedRestriction_surjective : Function.Surjective (wholePlaneGradedRestriction t I) := by
  intro y
  exact ⟨wholePlaneGradedInclusion t I hH y,
    DFunLike.congr_fun (wholePlaneGradedRestriction_comp_inclusion t I hH) y⟩

theorem wholePlaneGradedInclusion_surjective : Function.Surjective (wholePlaneGradedInclusion t I hH) := by
  intro x
  exact ⟨wholePlaneGradedRestriction t I x,
    DFunLike.congr_fun (wholePlaneGradedInclusion_comp_restriction t I hH) x⟩

end PfaffianDescent.Coray

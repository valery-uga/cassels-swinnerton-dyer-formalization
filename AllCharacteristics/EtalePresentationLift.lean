import AllCharacteristics.JacobianLocalization
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Lifting an étale presentation by localizing its Jacobian

Relations are lifted through the original coefficient map. Localizing the
resulting model at its Jacobian preserves the original algebra after base
change, and gives an étale lift when the relative dimension is zero.
-/

open scoped TensorProduct
open Algebra
namespace AllCharacteristics
universe u v w i j
variable (A : Type u) {S : Type v} {T : Type w}
variable [CommRing A] [CommRing S] [CommRing T]
variable [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
variable {ι : Type i} {σ : Type j} [Finite σ]
variable (P : Algebra.SubmersivePresentation S T ι σ)

/-- A surjective coefficient map contains every coefficient needed by the presentation. -/
lemma submersivePresentation_hasCoeffs_of_surjective
    (h : Function.Surjective (algebraMap A S)) : P.HasCoeffs A :=
  ⟨fun c _ => h c⟩

variable [P.HasCoeffs A]

/-- The model Jacobian is the quotient class of the lifted determinant. -/
lemma jacobian_ofHasCoeffs_eq :
    (P.toPreSubmersivePresentation.ofHasCoeffs A).jacobian =
      Ideal.Quotient.mk _ (P.jacobianOfHasCoeffs A) := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rfl

/-- The lifted Jacobian maps to the original Jacobian under the actual base-change isomorphism. -/
lemma tensorModelOfHasCoeffsEquiv_jacobian :
    P.toPresentation.tensorModelOfHasCoeffsEquiv A
      (1 ⊗ₜ[A] (P.toPreSubmersivePresentation.ofHasCoeffs A).jacobian) = P.jacobian := by
  rw [jacobian_ofHasCoeffs_eq]
  simp only [Algebra.Presentation.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
    Algebra.SubmersivePresentation.aeval_jacobianOfHasCoeffs]

/-- The lifted Jacobian is already a unit after the original base change. -/
lemma isUnit_tensorModel_jacobian :
    IsUnit ((1 : S) ⊗ₜ[A] (P.toPreSubmersivePresentation.ofHasCoeffs A).jacobian) := by
  have h := P.jacobian_isUnit.map (P.toPresentation.tensorModelOfHasCoeffsEquiv A).symm
  rw [← tensorModelOfHasCoeffsEquiv_jacobian A P] at h
  simpa only [AlgEquiv.symm_apply_apply] using h

/-- The lifted presentation with its Jacobian inverted. -/
noncomputable abbrev localizedPresentationModel :=
  Localization.Away (P.toPreSubmersivePresentation.ofHasCoeffs A).jacobian

/-- The localized lift is étale when the presentation has relative dimension zero. -/
lemma etale_localizedPresentationModel [Finite ι] (h : P.dimension = 0) :
    Algebra.Etale A (localizedPresentationModel A P) :=
  etale_jacobianLocalization_of_dimension_zero
    (P.toPreSubmersivePresentation.ofHasCoeffs A) h

/-- Base change of the localized lift recovers the original algebra. -/
noncomputable def tensorLocalizedPresentationModelEquiv :
    S ⊗[A] localizedPresentationModel A P ≃ₐ[S] T :=
  (IsLocalization.Away.tensorProductEquivTMulRight A S
    (P.toPreSubmersivePresentation.ofHasCoeffs A).jacobian
    (localizedPresentationModel A P)).trans
    (((IsLocalization.atUnit (S ⊗[A] P.toPresentation.ModelOfHasCoeffs A)
      (Localization.Away ((1 : S) ⊗ₜ[A] (P.toPreSubmersivePresentation.ofHasCoeffs A).jacobian))
      ((1 : S) ⊗ₜ[A] (P.toPreSubmersivePresentation.ofHasCoeffs A).jacobian)
      (isUnit_tensorModel_jacobian A P)).symm.restrictScalars S).trans
      (P.toPresentation.tensorModelOfHasCoeffsEquiv A))

/-- The recovery isomorphism agrees with the original coefficient-model isomorphism. -/
lemma tensorLocalizedPresentationModelEquiv_tmul (s : S)
    (x : P.toPresentation.ModelOfHasCoeffs A) :
    tensorLocalizedPresentationModelEquiv A P
      (s ⊗ₜ[A] algebraMap _ (localizedPresentationModel A P) x) =
        P.toPresentation.tensorModelOfHasCoeffsEquiv A (s ⊗ₜ[A] x) := by
  simp only [tensorLocalizedPresentationModelEquiv, AlgEquiv.trans_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul, AlgEquiv.coe_restrictScalars,
    AlgEquiv.commutes, Algebra.algebraMap_self_apply]

end AllCharacteristics

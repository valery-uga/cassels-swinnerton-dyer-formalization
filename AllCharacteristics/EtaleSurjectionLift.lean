import AllCharacteristics.EtalePresentationLift
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Lifting étale algebras through a surjective coefficient map

An actual étale lift is constructed from a finite presentation and its
Jacobian. Its original base-change square is a pushout, and the lifted
algebra maps surjectively onto the original étale algebra.
-/

open scoped TensorProduct
open Algebra
namespace AllCharacteristics
universe u v w
variable (A : Type u) (S : Type v) (T : Type w)
variable [CommRing A] [CommRing S] [CommRing T]
variable [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]

/-- Every étale algebra lifts through a surjective coefficient map, with an actual
pushout square and a surjective map from the lift. -/
theorem exists_etaleLift_of_surjective [Algebra.Etale S T]
    (h : Function.Surjective (algebraMap A S)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra B T),
      ∃ (_ : IsScalarTower A B T), Algebra.Etale A B ∧ Algebra.IsPushout A S B T ∧
        Function.Surjective (algebraMap B T) := by
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 S T :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (R := S) (S := T) (n := 0)
  have : P.HasCoeffs A := submersivePresentation_hasCoeffs_of_surjective A P h
  let B := localizedPresentationModel A P
  let e : S ⊗[A] B ≃ₐ[S] T := tensorLocalizedPresentationModelEquiv A P
  let g : B →ₐ[A] T := (e.toAlgHom.restrictScalars A).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[A] S ⊗[A] B)
  let : Algebra B T := g.toAlgebra
  have : IsScalarTower A B T :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    etale_localizedPresentationModel A P hP, ?_, ?_⟩
  · exact ⟨IsBaseChange.of_equiv e.toLinearEquiv (fun _ => rfl)⟩
  · exact e.surjective.comp (Algebra.TensorProduct.includeRight_surjective B h)

end AllCharacteristics

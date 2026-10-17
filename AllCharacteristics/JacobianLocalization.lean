import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Inverting the Jacobian of a finite presentation

Localizing a presubmersive presentation at its Jacobian produces an actual
submersive presentation, without a hypothesis on the coefficient map.
-/

open Algebra
namespace AllCharacteristics
universe u v w t
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} {σ : Type t} [Finite ι] [Finite σ]
variable (P : Algebra.PreSubmersivePresentation R S ι σ)

/-- The presentation obtained by adjoining the inverse Jacobian. -/
noncomputable def jacobianLocalizedPresentation :
    Algebra.SubmersivePresentation R (Localization.Away P.jacobian) (Unit ⊕ ι) (Unit ⊕ σ) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway (Localization.Away P.jacobian) P.jacobian).comp P
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
      (IsLocalization.Away.algebraMap_isUnit P.jacobian)

/-- Adjoining an inverse adds one variable and one relation. -/
theorem jacobianLocalizedPresentation_dimension :
    (jacobianLocalizedPresentation P).dimension = P.dimension := by
  change ((Algebra.PreSubmersivePresentation.localizationAway
    (Localization.Away P.jacobian) P.jacobian).comp P).dimension = P.dimension
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  change (Nat.card Unit - Nat.card Unit) + P.dimension = P.dimension
  rw [Nat.sub_self, Nat.zero_add]

/-- A presentation with equally many variables and relations becomes étale
after its Jacobian is inverted. -/
theorem etale_jacobianLocalization_of_dimension_zero (h : P.dimension = 0) :
    Algebra.Etale R (Localization.Away P.jacobian) := by
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 R (Localization.Away P.jacobian) :=
    (jacobianLocalizedPresentation P).isStandardSmoothOfRelativeDimension
      ((jacobianLocalizedPresentation_dimension P).trans h)
  infer_instance

end AllCharacteristics

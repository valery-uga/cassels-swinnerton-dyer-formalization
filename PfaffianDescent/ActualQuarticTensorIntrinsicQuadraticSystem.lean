import PfaffianDescent.ActualQuarticTensorFullQuadraticKernel
import PfaffianDescent.FourTangentIntrinsicQuadraticSystem

/-! The intrinsic full quadratic series of the actual tensor coordinate
point. Its unit coordinate is derived from the original dual presentation;
the full series is transported to the actual four-tangent full series.
The original scheme's ambient base-change square is a separate obligation. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- On a normalized finite point with a unit coordinate, intrinsic
scheme-theoretic quadrics are exactly its actual algebra evaluation kernel.
No radical or reduced-support ideal occurs. -/
theorem linearNormalizedPoint_intrinsicQuadraticSystem_eq_evaluation_of_unit_coordinate
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hOne : ell.eval₂ (algebraMap K A) x = 1)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) x = 0)
    (j : Fin 4) (u : Aˣ) (hu : (u : A) = x j) :
    intrinsicFullQuadraticSystem
      (linearNormalizedPoint I x ell hell hOne he ≫ quotientProjMap I) =
      homogeneousVanishingPolynomialSubmodule x 2 := by
  apply le_antisymm
  · intro p hp
    apply (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 p).mpr
    exact ⟨hp.1,
      linearNormalizedPoint_intrinsicQuadratics_evaluation_zero_of_unit_coordinate
        I x ell hell hOne he j u hu p hp⟩
  · simpa only [normalizedFiniteEquationPoint, linearNormalizedPointAt,
      linearNormalizedPoint, linearNormalizedPointChartMapAt,
      linearNormalizedPointChartMap] using
      normalizedFiniteEquationPoint_evaluationQuadrics_le_intrinsic
        I x ell hell hOne he

namespace QuarticNet
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]

/-- The original normalized coordinate remains literally one after
scalar extension. This follows from the actual dual presentation. -/
theorem actualQuarticTensor_zero_coordinate_eq_one
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0) :
    (1 : K) ⊗ₜ[k] x 0 = (1 : K ⊗[k] A) := by
  have hx0 : x 0 = 1 := eA.injective (by rw [hx 0, hb, hv]; simp)
  rw [hx0]
  rfl

private theorem actualQuarticTensor_normalizer_eval
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0) :
    (X (0 : Fin 4) : MvPolynomial (Fin 4) K).eval₂
      (algebraMap K (K ⊗[k] A)) (fun r => (1 : K) ⊗ₜ[k] x r) = 1 := by
  rw [eval₂_X]
  exact actualQuarticTensor_zero_coordinate_eq_one eA x b v hx hb hv

private theorem actualQuarticTensor_bot_equations
    (x : Fin 4 → A) : ∀ p ∈
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)).toIdeal,
      p.eval₂ (algebraMap K (K ⊗[k] A)) (fun r => (1 : K) ⊗ₜ[k] x r) = 0 := by
  intro p hp
  have hp0 : p = 0 := Ideal.mem_bot.mp hp
  simp [hp0]

/-- The actual tensor-algebra normalized point, with coordinate zero one
derived internally. It uses the original algebra elements x. -/
def actualQuarticTensorNormalizedToProjective
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0) :
    Spec (.of (K ⊗[k] A)) ⟶
      scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :=
  linearNormalizedPoint ⊥ (fun r => (1 : K) ⊗ₜ[k] x r) (X (0 : Fin 4))
    (isHomogeneous_X K 0) (actualQuarticTensor_normalizer_eval eA x b v hx hb hv)
    (actualQuarticTensor_bot_equations x)

theorem actualQuarticTensor_intrinsicQuadraticSystem_eq_kernel
    [FiniteDimensional k A]
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0) :
    intrinsicFullQuadraticSystem
      (actualQuarticTensorNormalizedToProjective (K := K) eA x b v hx hb hv ≫
        quotientProjMap ⊥) = homogeneousVanishingPolynomialSubmodule
          (K := K) (fun r => (1 : K) ⊗ₜ[k] x r) 2 := by
  unfold actualQuarticTensorNormalizedToProjective
  exact linearNormalizedPoint_intrinsicQuadraticSystem_eq_evaluation_of_unit_coordinate
    ⊥ _ _ _ _ _ 0 (1 : (K ⊗[k] A)ˣ)
      (actualQuarticTensor_zero_coordinate_eq_one eA x b v hx hb hv).symm

/-- Entire intrinsic full-series equality at the actual tensor point and
the actual normalized tangent point, under the same derived substitution. -/
theorem actualQuarticTensor_intrinsicFullQuadraticSystem_map
    [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [FiniteDimensional k A]
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b 0 = 1) (hv : v 0 = 0)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ row, l row ≠ 0) :
    let hs := conjugate_basis_span b full
    let cb := conjugateBasis full b hs
    let ep := linearSubstitutionEquiv (basisCoordinateMatrix cb) (basisCoordinateMatrix_isUnit cb)
    let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
    (intrinsicFullQuadraticSystem
      (actualQuarticTensorNormalizedToProjective (K := K) eA x b v hx hb hv ≫
        quotientProjMap ⊥)).map ep.toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem (fourTangentDualToProjective U ≫ quotientProjMap ⊥) := by
  let hs := conjugate_basis_span b full
  let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
  have hdiag : ∀ row, U row row = 0 := by
    intro row
    simp only [U, rescaleTangentDirections,
      conjugateTangentMatrix_diagonal full b v hs row, mul_zero]
  dsimp only
  rw [actualQuarticTensor_intrinsicQuadraticSystem_eq_kernel,
    fourTangent_intrinsicQuadraticSystem_eq_normalizedKernel U hdiag]
  exact actualQuarticTensor_fullQuadraticKernel_eq eA x b v hx full l hl

end QuarticNet
end PfaffianDescent

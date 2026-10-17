import PfaffianDescent.IntrinsicQuadraticCoordinatePermutation
import PfaffianDescent.ActualQuarticDualTensorCoordinates
import AllCharacteristics.FiniteFlatCycle
import Mathlib.RingTheory.TensorProduct.Finite

/-! Generation and rank of the actual tensor coordinate immersion, derived
from the original coordinate evaluator and the literal tensor algebra. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem tensorCoordinates_aeval_map
    {k K A : Type u} [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (x : Fin 4 → A)
    (p : MvPolynomial (Fin 4) k) :
    aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] x r)
      (map (algebraMap k K) p) = (1 : K) ⊗ₜ[k] aeval (R := k) x p := by
  rw [aeval_def, eval₂_map]
  rw [← IsScalarTower.algebraMap_eq k K (K ⊗[k] A)]
  change aeval (R := k) (fun r => (1 : K) ⊗ₜ[k] x r) p =
    (1 : K) ⊗ₜ[k] aeval (R := k) x p
  rw [MvPolynomial.aeval_one_tmul]

theorem tensorCoordinates_aeval_surjective
    {k K A : Type u} [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] (x : Fin 4 → A)
    (hgen : Function.Surjective (aeval (R := k) x)) :
    Function.Surjective (aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] x r)) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c a =>
    obtain ⟨p, hp⟩ := hgen a
    refine ⟨C c * map (algebraMap k K) p, ?_⟩
    rw [map_mul, aeval_C, tensorCoordinates_aeval_map, hp]
    simp only [Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add z w hz hw =>
    obtain ⟨p, hp⟩ := hz
    obtain ⟨q, hq⟩ := hw
    exact ⟨p + q, by rw [map_add, hp, hq]⟩

theorem ambientNormalizedCoordinateChartPoint_isClosedImmersion
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1)
    (hgen : Function.Surjective (aeval (R := K) x)) :
    IsClosedImmersion (ambientNormalizedCoordinateChartPoint (F := K) x j hx) := by
  have he : ∀ p ∈ (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)).toIdeal,
      p.eval₂ (algebraMap K A) x = 0 := by
    intro p hp
    simp [Ideal.mem_bot.mp hp]
  let q := linearNormalizedPoint ⊥ x (X j) (isHomogeneous_X K j)
    (by simpa only [eval₂_X] using hx) he
  letI : IsClosedImmersion q :=
    linearNormalizedPointAt_isClosedImmersion _ _ _ _ _ _ hgen
  rw [← linearNormalizedPoint_toAmbient_eq_coordinateChartPoint ⊥ x j hx he]
  exact inferInstanceAs (IsClosedImmersion (q ≫ quotientProjMap ⊥))

theorem ambientNormalizedCoordinateChartPoint_finite_toBase
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1) :
    IsFinite (ambientNormalizedCoordinateChartPoint (F := K) x j hx ≫ ambientToBase) := by
  rw [ambientNormalizedCoordinateChartPoint_toBase]
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

theorem ambientNormalizedCoordinateChartPoint_finiteSchemeRank
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1) :
    letI := ambientNormalizedCoordinateChartPoint_finite_toBase (K := K) x j hx
    AllCharacteristics.finiteSchemeRank
      (ambientNormalizedCoordinateChartPoint (F := K) x j hx ≫ ambientToBase) =
      Module.finrank K A := by
  letI := ambientNormalizedCoordinateChartPoint_finite_toBase (K := K) x j hx
  rw [AllCharacteristics.finiteSchemeRank_eq_finrank,
    ambientNormalizedCoordinateChartPoint_toBase,
    Scheme.Hom.finrank_SpecMap_algebraMap]
  exact congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := A)) _

namespace QuarticNet
theorem actualQuarticTensor_finrank_eight
    {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
    [Algebra k L] [Algebra k K] [Algebra k A]
    [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (eA : A ≃ₐ[k] DualNumber L) (b : Basis (Fin 4) k L)
    (full : Fin 4 ≃ (L →ₐ[k] K)) :
    Module.finrank K (K ⊗[k] A) = 8 :=
  (actualQuarticDualTensorEquiv eA b full).toLinearEquiv.finrank_eq.trans
    (fourTangentDualAlgebra_finrank (K := K))
end QuarticNet
end PfaffianDescent

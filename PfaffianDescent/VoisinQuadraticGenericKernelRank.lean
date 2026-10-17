import PfaffianDescent.VoisinQuadraticEvaluationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A unit quadratic evaluation minor gives a rank-two kernel

Eight independent evaluation rows among the ten quadratic monomials
force the full homogeneous quadratic evaluation kernel to have
dimension two. This avoids a choice of complementary monomial columns.
-/

namespace PfaffianDescent

open AllCharacteristics.UniversalHomogeneous
open Module

universe u

theorem eightPointQuadraticEvaluationMatrix_kernel_finrank_two
    {F : Type u} [Field F]
    (y : Fin 8 → Fin 4 → F)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m y).det) :
    Module.finrank F
      (LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y))) = 2 := by
  let M := eightPointQuadraticEvaluationMatrix y
  have hunit : IsUnit (M.submatrix id m) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hm
  have hminor : (M.submatrix id m).rank = 8 := by
    simpa using Matrix.rank_of_isUnit (M.submatrix id m) hunit
  have hlow : 8 ≤ M.rank := by
    simpa only [hminor] using Matrix.rank_submatrix_le M id m
  have hhigh : M.rank ≤ 8 := by
    simpa using Matrix.rank_le_card_height M
  have hrank : M.rank = 8 := le_antisymm hhigh hlow
  have hrange : Module.finrank F (LinearMap.range (Matrix.toLin' M)) = 8 := by
    exact (Matrix.rank_eq_finrank_range_toLin M
      (Pi.basisFun F (Fin 8))
      (Pi.basisFun F (Monomials (Fin 4) 2))).symm.trans hrank
  have hsource : Module.finrank F (Monomials (Fin 4) 2 → F) = 10 := by
    simp [quadraticMonomials_card]
  have hsum := (Matrix.toLin' M).finrank_range_add_finrank_ker
  rw [hrange, hsource] at hsum
  change Module.finrank F (LinearMap.ker (Matrix.toLin' M)) = 2
  omega

/-- A chosen full-rank minor gives a two-element basis of the full
quadratic evaluation kernel over the generic field. -/
noncomputable def eightPointQuadraticEvaluationMatrix_kernelBasis
    {F : Type u} [Field F]
    (y : Fin 8 → Fin 4 → F)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m y).det) :
    Basis (Fin 2) F
      (LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y))) := by
  classical
  have hdim := eightPointQuadraticEvaluationMatrix_kernel_finrank_two y m hm
  simpa only [hdim] using
    (Module.finBasis F
      (LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y))))

end PfaffianDescent

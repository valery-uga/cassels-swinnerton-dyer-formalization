import PfaffianDescent.QuarticTangentRelabeling

/-!
# Rescaling tangent directions

Changing a tangent-vector representative by a scalar preserves the
corresponding first-order vanishing condition.  This lets the skew
normalization be used by the explicit net calculations.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

variable {K : Type*} [Field K]

noncomputable def dualNumberRescale (c : K) : DualNumber K →ₐ[K] DualNumber K :=
  TrivSqZeroExt.map (LinearMap.mulLeft K c)

theorem rescaleTangentDirections_vanishing (U : Fin 4 → Fin 4 → K) (l : Fin 4 → K)
    (F : MvPolynomial (Fin 4) K)
    (hF : ∀ i, aeval (tangentDualPoint U i) F = 0) :
    ∀ i, aeval (tangentDualPoint (rescaleTangentDirections l U) i) F = 0 := by
  intro i
  have h : (dualNumberRescale (l i)).comp (aeval (tangentDualPoint U i)) =
      aeval (tangentDualPoint (rescaleTangentDirections l U) i) := by
    ext j : 1
    simp only [AlgHom.comp_apply, aeval_X]
    apply TrivSqZeroExt.ext <;>
      simp [dualNumberRescale, tangentDualPoint, rescaleTangentDirections,
        TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map] <;> ring
  rw [← AlgHom.congr_fun h F, AlgHom.comp_apply, hF i, map_zero]

theorem rescaleTangentDirections_nonzero (U : Fin 4 → Fin 4 → K) (l : Fin 4 → K)
    (hl : ∀ i, l i ≠ 0) (i j : Fin 4) :
    rescaleTangentDirections l U i j ≠ 0 ↔ U i j ≠ 0 := by
  simp [rescaleTangentDirections, hl]

/-- A skew matrix with zero diagonal is determined by its six upper-triangular
entries. -/
theorem skew_matrix_eq_parameters (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i) :
    U = skewTangentDirections (U 0 1) (U 0 2) (U 0 3)
      (U 1 2) (U 1 3) (U 2 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewTangentDirections, hdiag]
  all_goals exact hskew _ _

end QuarticNet
end PfaffianDescent

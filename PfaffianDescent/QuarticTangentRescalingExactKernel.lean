import PfaffianDescent.QuarticTangentRescaling

/-! Nonzero tangent rescaling preserves exact entire-polynomial kernels,
including all nilpotent conditions. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial Module TrivSqZeroExt
variable {K : Type*} [Field K]

theorem dualNumberRescale_injective {c : K} (hc : c ≠ 0) :
    Function.Injective (dualNumberRescale c) := by
  intro a b hab
  apply TrivSqZeroExt.ext
  · simpa [dualNumberRescale, TrivSqZeroExt.fst_map] using
      congrArg TrivSqZeroExt.fst hab
  · apply mul_left_cancel₀ hc
    simpa [dualNumberRescale, TrivSqZeroExt.snd_map] using
      congrArg TrivSqZeroExt.snd hab

/-- The equation kernel is equal even for inhomogeneous polynomials, at each
individual double point; a nonzero row multiplier changes only its epsilon. -/
theorem rescaleTangentDirections_equation_iff
    (U : Fin 4 → Fin 4 → K) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (F : MvPolynomial (Fin 4) K) (i : Fin 4) :
    aeval (tangentDualPoint (rescaleTangentDirections l U) i) F = 0 ↔
      aeval (tangentDualPoint U i) F = 0 := by
  have h : (dualNumberRescale (l i)).comp (aeval (tangentDualPoint U i)) =
      aeval (tangentDualPoint (rescaleTangentDirections l U) i) := by
    ext j : 1
    simp only [AlgHom.comp_apply, aeval_X]
    apply TrivSqZeroExt.ext <;>
      simp [dualNumberRescale, tangentDualPoint, rescaleTangentDirections,
        TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map] <;> ring
  rw [← AlgHom.congr_fun h F, AlgHom.comp_apply]
  constructor
  · intro hz
    exact dualNumberRescale_injective (hl i) (by simpa using hz)
  · intro hz
    rw [hz, map_zero]

end PfaffianDescent.QuarticNet

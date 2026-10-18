import AllCharacteristics.ReframeCommonTangentLine
import Mathlib.Algebra.MvPolynomial.Funext

/-! A nonzero common-line restriction supplies an actual
noncubic point, then the split kernel frame is reframed to begin with it. -/

noncomputable section
namespace PfaffianDescent
open MvPolynomial
universe u

theorem rectangularSubstitution_eval_any_dimensions
    {K : Type u} [Field K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) K) (x : Fin n → K)
    (F : MvPolynomial (Fin m) K) :
    MvPolynomial.eval x (rectangularSubstitution M F) =
      MvPolynomial.eval (M.mulVec x) F := by
  have h : (MvPolynomial.aeval x).comp (rectangularSubstitution M) =
      MvPolynomial.aeval (M.mulVec x) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, rectangularSubstitution_X, aeval_X]
    have he := eval₂_rectangularLinearCoordinate M i (RingHom.id K) x
    have hMid : M.map (RingHom.id K) = M := by
      ext i j
      rfl
    rw [hMid] at he
    simpa only [aeval_def, Algebra.algebraMap_self] using he
  simpa only [AlgHom.comp_apply, aeval_def, Algebra.algebraMap_self,
    MvPolynomial.eval₂_id] using
    AlgHom.congr_fun h F

theorem exists_noncubic_value_of_line_restriction_ne_zero
    {K : Type u} [Field K] [Infinite K]
    (c : Cubic K 4) (A : Matrix (Fin 4) (Fin 2) K)
    (hrest : rectangularSubstitution A c.toMvPolynomial ≠ 0) :
    ∃ u : Fin 2 → K, c.eval (A.mulVec u) ≠ 0 := by
  by_contra h
  push Not at h
  apply hrest
  apply MvPolynomial.funext
  intro x
  rw [_root_.map_zero, rectangularSubstitution_eval_any_dimensions]
  have he := Cubic.eval_toMvPolynomial (RingHom.id K) c (A.mulVec x)
  rw [MvPolynomial.eval₂_id,
    show c.map (RingHom.id K) = c by funext i; rfl] at he
  rw [he, h x]

theorem exists_split_common_line_frame_with_noncubic_first_column
    {K : Type u} [Field K] [Infinite K]
    (R : Matrix (Fin 2) (Fin 4) K)
    (A : Matrix (Fin 4) (Fin 2) K) (B : Matrix (Fin 2) (Fin 4) K)
    (S : Matrix (Fin 4) (Fin 2) K)
    (hBA : B * A = 1) (hRA : R * A = 0) (hRS : R * S = 1)
    (c : Cubic K 4)
    (hrest : rectangularSubstitution A c.toMvPolynomial ≠ 0) :
    ∃ (A' : Matrix (Fin 4) (Fin 2) K) (B' : Matrix (Fin 2) (Fin 4) K),
      B' * A' = 1 ∧ R * A' = 0 ∧
      c.eval (fun i ↦ A' i 0) ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_noncubic_value_of_line_restriction_ne_zero c A hrest
  exact exists_split_kernel_frame_first_column_nonzero_cubic_value
    R A B S hBA hRA hRS c u hu

end PfaffianDescent

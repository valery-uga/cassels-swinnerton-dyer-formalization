import AllCharacteristics.OriginalGlobalHilbertCubicSubschemeLifting
import AllCharacteristics.InternalCorayPaperConclusions

/-! Literal ChapterFiveLiftFor supplied by the ACTUAL global Hilbert
family route. The selected-point smooth theorem uses the accepted internal
Coray and native geometric factory. Its terminal Chapter3 dependencies are
reported under the manuscript's permitted mixed scope, not suppressed. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory
open HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The full original Chapter5 lifting proposition is supplied by the
new global universal-family construction, for the exact original field. -/
theorem chapterFiveLiftFor_viaGlobalHilbert001 {k : Type u} [Field k] :
    ChapterFiveLiftFor k := by
  intro ell _ _ p hp hne hs x
  letI : Smooth (hypersurfaceToBase p hp) := hs
  exact exists_smooth_charZero_cubic_lift_with_original_closed_subscheme_viaGlobalHilbert001
    ell hp hne x

/-- The unrestricted positive-characteristic Chapter5 lifting statement,
with no Cohen/DVR/Hilbert/lift outcome input, via the actual global family. -/
theorem chapterFiveLiftStatement_viaGlobalHilbert001 : ChapterFiveLiftStatement.{u} := by
  intro k hField ell hPrime hChar
  exact chapterFiveLiftFor_viaGlobalHilbert001 (k := k)

/-- The selected-point proof of the original smooth-surface conclusion,
with ChapterFiveLiftFor supplied by the ACTUAL global Hilbert family and
Coray/native geometry supplied internally. This terminal proof retains the
manuscript's permitted mixed Chapter3 route and is audited in that scope. -/
theorem twoProofs_chapterFive_smooth_by_selected_closedPoint_viaGlobalHilbert_internalCoray001
    {k : Type u} [Field k] (ell : ℕ) [Fact ell.Prime] [CharP k ell]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (w : ZeroCycle (hypersurface p hp))
    (hw : ZeroCycle.degree (hypersurfaceToBase p hp) w = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  twoProofs_chapterFive_smooth_of_lift_by_selected_closedPoint
    internalCorayDegreeOneFourOrTenFor_uniform001 ell
    (chapterFiveLiftFor_viaGlobalHilbert001 (k := k)) p hp hne w hw

end AllCharacteristics
end

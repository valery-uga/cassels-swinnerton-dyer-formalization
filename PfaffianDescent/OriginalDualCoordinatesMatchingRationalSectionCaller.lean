import PfaffianDescent.ConjugateQuarticAnyChartZeroEntrySupportGraph
import PfaffianDescent.SuppliedFrameTangentWeights
import PfaffianDescent.OriginalDualCoordinatesMatchingMethodParameters
import PfaffianDescent.ActualOriginalMatchingQuadraticLinePair
import PfaffianDescent.OriginalMatchingBranchRationalSectionCaller
import PfaffianDescent.OriginalDualCoordinatesAnyChartFourCycleFinite

/-! SOURCE ONLY. Actual original dual coordinates derive the matching
normal form, tangent vanishing, quadratic field and section internally.
The four-cycle alternative remains literal ground full-base finiteness. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L A : Type u} [Field k] [PerfectField k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] [FiniteDimensional k L]
  [Algebra.IsSeparable k L] [FiniteDimensional k A]

theorem originalDualCoordinates_any_chart_zero_entry_rational_section_or_finite
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (j : Fin 4) (hxj : x j = 1) (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b j = 1) (hv : v j = 0) (hvne : v ≠ 0)
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (hFx : aeval (R := k) x F = 0)
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0) :
    let U := rescaleTangentDirections l
      (conjugateTangentMatrix full b v (conjugate_basis_span b full))
    (∀ r s, U r s = -U s r) →
    (∃ r s, r ≠ s ∧ U r s = 0) →
    (Scheme.IsRationalOver (hypersurfaceToBase F hF) ∧
      ∃ s : Spec (.of k) ⟶ hypersurface F hF, s ≫ hypersurfaceToBase F hF = 𝟙 _) ∨
      IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
        (ambientNormalizedCoordinateChartPoint (F := k) x j hxj))) := by
  classical
  dsimp only
  intro hskew hmissing
  let hs := conjugate_basis_span b full
  let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
  have hClass := conjugateQuartic_any_chart_zero_entry_support_graph
    full b v hs j hb hv hvne l hl hskew hmissing
  obtain ⟨rho, hmatch | hcycle⟩ := hClass.2
  · let V := tangentRelabel U rho
    have hVskew (r s : Fin 4) : V r s = -V s r := hskew (rho r) (rho s)
    have hne (r s : Fin 4) (h : coordinateMatchingAdj r s) : V r s ≠ 0 :=
      (hmatch r s).mpr h
    have hz (r s : Fin 4) (h : ¬ coordinateMatchingAdj r s) : V r s = 0 := by
      by_contra hzero
      exact h ((hmatch r s).mp hzero)
    obtain ⟨a, f, ha, hf, hU, hvan⟩ :=
      originalDualCoordinates_matching_method_parameters
        eA x b v hx full l hl rho hVskew
        (hne 0 1 (by simp [coordinateMatchingAdj]))
        (hne 2 3 (by simp [coordinateMatchingAdj]))
        (hz 0 2 (by simp [coordinateMatchingAdj]))
        (hz 0 3 (by simp [coordinateMatchingAdj]))
        (hz 1 2 (by simp [coordinateMatchingAdj]))
        (hz 1 3 (by simp [coordinateMatchingAdj])) F hF hFx
    exact Or.inl (originalMatchingBranch_original_cubic_rational_and_section
      full b v hs l hl rho a f ha hf hU F hF hF₀ hvan)
  · let V := tangentRelabel U rho
    have hVskew (r s : Fin 4) : V r s = -V s r := hskew (rho r) (rho s)
    have hne (r s : Fin 4) (h : coordinateFourCycleAdj r s) : V r s ≠ 0 :=
      (hcycle r s).mpr h
    have hz (r s : Fin 4) (h : ¬ coordinateFourCycleAdj r s) : V r s = 0 := by
      by_contra hzero
      exact h ((hcycle r s).mp hzero)
    exact Or.inr
      (originalDualCoordinates_any_chart_fourCycle_groundFullBase_isFinite
        eA x j hxj b v hx hb hv full l hl rho hVskew
        (hz 0 1 (by simp [coordinateFourCycleAdj]))
        (hz 2 3 (by simp [coordinateFourCycleAdj]))
        (hne 0 2 (by simp [coordinateFourCycleAdj]))
        (hne 0 3 (by simp [coordinateFourCycleAdj]))
        (hne 1 2 (by simp [coordinateFourCycleAdj]))
        (hne 1 3 (by simp [coordinateFourCycleAdj])))

theorem originalDualCoordinates_any_chart_matching_rational_and_section
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (j : Fin 4) (hxj : x j = 1) (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b j = 1) (hv : v j = 0) (hvne : v ≠ 0)
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (hFx : aeval (R := k) x F = 0)
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0) :
    let U := rescaleTangentDirections l
      (conjugateTangentMatrix full b v (conjugate_basis_span b full))
    (∀ r s, U r s = -U s r) →
    (∃ r s, r ≠ s ∧ U r s = 0) →
    (∀ r, ∃! s, U r s ≠ 0) →
    Scheme.IsRationalOver (hypersurfaceToBase F hF) ∧
      ∃ s : Spec (.of k) ⟶ hypersurface F hF, s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  classical
  dsimp only
  intro hskew hmissing hOne
  let hs := conjugate_basis_span b full
  let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
  have hClass := conjugateQuartic_any_chart_zero_entry_support_graph
    full b v hs j hb hv hvne l hl hskew hmissing
  obtain ⟨rho, hmatch | hcycle⟩ := hClass.2
  · let V := tangentRelabel U rho
    have hVskew (r s : Fin 4) : V r s = -V s r := hskew (rho r) (rho s)
    have hne (r s : Fin 4) (h : coordinateMatchingAdj r s) : V r s ≠ 0 :=
      (hmatch r s).mpr h
    have hz (r s : Fin 4) (h : ¬ coordinateMatchingAdj r s) : V r s = 0 := by
      by_contra hzero
      exact h ((hmatch r s).mp hzero)
    obtain ⟨a, f, ha, hf, hU, hvan⟩ :=
      originalDualCoordinates_matching_method_parameters
        eA x b v hx full l hl rho hVskew
        (hne 0 1 (by simp [coordinateMatchingAdj]))
        (hne 2 3 (by simp [coordinateMatchingAdj]))
        (hz 0 2 (by simp [coordinateMatchingAdj]))
        (hz 0 3 (by simp [coordinateMatchingAdj]))
        (hz 1 2 (by simp [coordinateMatchingAdj]))
        (hz 1 3 (by simp [coordinateMatchingAdj])) F hF hFx
    exact originalMatchingBranch_original_cubic_rational_and_section
      full b v hs l hl rho a f ha hf hU F hF hF₀ hvan
  · obtain ⟨s, hsNonzero, hsUnique⟩ := hOne (rho 0)
    have h02 : U (rho 0) (rho 2) ≠ 0 :=
      (hcycle 0 2).mpr (by simp [coordinateFourCycleAdj])
    have h03 : U (rho 0) (rho 3) ≠ 0 :=
      (hcycle 0 3).mpr (by simp [coordinateFourCycleAdj])
    have he : rho 2 = rho 3 := (hsUnique (rho 2) h02).trans (hsUnique (rho 3) h03).symm
    exact False.elim ((by decide : (2 : Fin 4) ≠ 3) (rho.injective he))

end PfaffianDescent.QuarticNet

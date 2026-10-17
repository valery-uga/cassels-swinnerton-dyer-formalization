import PfaffianDescent.CorayOriginalChartFunctionFieldGeneration
import Mathlib.Algebra.BigOperators.Field

/-! Actual original affine-chart coefficients clear to one original denominator.
This constructs the next algebraic input to tangent-pair incidence polynomial
clearing, using the existing true original function-field fraction theorem. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
universe u
set_option autoImplicit false

/-- Every finite family in the actual original function field has one
nonzero actual affine-chart denominator and actual affine-chart numerators.
No fraction presentation or nonzero denominator certificate is supplied. -/
theorem affineChartGenericEvaluation_commonDenominator001
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of R) ⟶ X) [IsOpenImmersion i] [Nonempty i.opensRange]
    {m : ℕ} (c : Fin m → X.functionField) :
    ∃ d : R, affineChartGenericEvaluation i d ≠ 0 ∧
      ∃ A : Fin m → R,
        ∀ k, affineChartGenericEvaluation i (A k) =
          affineChartGenericEvaluation i d * c k := by
  classical
  let g := affineChartGenericEvaluation i
  choose a b hb hab using fun k => affineChartGenericEvaluation_div_surjective i (c k)
  let d : R := ∏ k, b k
  have hd : g d ≠ 0 := by
    dsimp only [d]
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hb k)
  refine ⟨d, hd, (fun k => a k * ∏ l ∈ Finset.univ.erase k, b l), ?_⟩
  intro k
  have hk : b k * (∏ l ∈ Finset.univ.erase k, b l) = d :=
    Finset.mul_prod_erase Finset.univ b (Finset.mem_univ k)
  have ha : g (a k) = c k * g (b k) := (div_eq_iff (hb k)).mp (hab k)
  change g (a k * ∏ l ∈ Finset.univ.erase k, b l) = g d * c k
  rw [map_mul, ha, ← hk, map_mul]
  ring

end PfaffianDescent.Coray

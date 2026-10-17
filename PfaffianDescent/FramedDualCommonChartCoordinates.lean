import PfaffianDescent.ActualLinearFrameNormalizedPointSquare
import PfaffianDescent.QuarticConjugateJets

/-! SOURCE ONLY, UNVERIFIED. Exact unit normalization of actual framed dual
points in a common ORIGINAL ambient chart, with nilpotents retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def framedDualRaw (b : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K) (i m : Fin 4) : DualNumber K :=
  ∑ s, algebraMap K (DualNumber K) (b s m) * tangentDualPoint U i s

theorem framedDualRaw_fst (b : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K) (i m : Fin 4) : (framedDualRaw b U i m).fst = b i m := by
  simp [framedDualRaw, tangentDualPoint, TrivSqZeroExt.fst_sum,
    TrivSqZeroExt.algebraMap_eq_inl, mul_ite, Finset.sum_ite_eq]

theorem framedDualRaw_snd (b : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K) (i m : Fin 4) :
    (framedDualRaw b U i m).snd = ∑ s, b s m * U i s := by
  simp [framedDualRaw, tangentDualPoint, TrivSqZeroExt.snd_sum,
    TrivSqZeroExt.algebraMap_eq_inl, DualNumber.snd_mul]

/-- Actual explicit unit; its inverse keeps the tangent coefficient. -/
noncomputable def framedDualChartUnit (b : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K) (i j : Fin 4) (hc : b i j ≠ 0) : (DualNumber K)ˣ where
  val := inl (b i j) + inr (∑ s, b s j * U i s)
  inv := inl (b i j)⁻¹ + inr (-(b i j)⁻¹ ^ 2 * (∑ s, b s j * U i s))
  val_inv := by
    apply TrivSqZeroExt.ext
    · simp [hc]
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_one, zero_add, add_zero, DualNumber.snd_mul]
      field_simp [hc]
      <;> ring
  inv_val := by
    apply TrivSqZeroExt.ext
    · simp [hc]
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_one, zero_add, add_zero, DualNumber.snd_mul]
      field_simp [hc]
      <;> ring

theorem framedDualRaw_chart_eq_unit (b : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K) (i j : Fin 4) (hc : b i j ≠ 0) :
    framedDualRaw b U i j = (framedDualChartUnit b U i j hc : DualNumber K) := by
  apply TrivSqZeroExt.ext
  · simpa only [framedDualChartUnit, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero] using framedDualRaw_fst b U i j
  · simpa only [framedDualChartUnit, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add] using framedDualRaw_snd b U i j

noncomputable def framedDualCommonChart (b : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K) (i j : Fin 4) (hc : b i j ≠ 0) : Fin 4 → DualNumber K :=
  fun m => (↑((framedDualChartUnit b U i j hc)⁻¹) : DualNumber K) * framedDualRaw b U i m

theorem framedDualCommonChart_one (b : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K) (i j : Fin 4) (hc : b i j ≠ 0) :
    framedDualCommonChart b U i j hc j = 1 := by
  unfold framedDualCommonChart
  rw [framedDualRaw_chart_eq_unit b U i j hc, Units.inv_mul]

/-- Exact ORIGINAL ambient embedding after the actual GL frame map. -/
theorem framedDual_common_chart_actual_square
    (b : Basis (Fin 4) K (Fin 4 → K)) (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (i j : Fin 4) (hc : b i j ≠ 0) :
    ambientNormalizedCoordinateChartPoint (F := K) (tangentDualPoint U i) i
      (by simp [tangentDualPoint, hdiag]) ≫
        (linearCoordinateChangeAmbientIso (basisCoordinateMatrix b)
          (basisCoordinateMatrix_isUnit b)).inv =
      ambientNormalizedCoordinateChartPoint (F := K) (framedDualCommonChart b U i j hc)
        j (framedDualCommonChart_one b U i j hc) := by
  let u := framedDualChartUnit b U i j hc
  let x : Fin 4 → DualNumber K := fun s => (↑(u⁻¹) : DualNumber K) * tangentDualPoint U i s
  have hCoords (m : Fin 4) :
      ((basisCoordinateMatrix b).map (algebraMap K (DualNumber K))).mulVec x m =
        framedDualCommonChart b U i j hc m := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, x, framedDualCommonChart,
      framedDualRaw, basisCoordinateMatrix, u]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hOne : ((basisCoordinateMatrix b).map (algebraMap K (DualNumber K))).mulVec x j = 1 :=
    (hCoords j).trans (framedDualCommonChart_one b U i j hc)
  let ell := linearCoordinate (basisCoordinateMatrix b) j
  have hell : ell.IsHomogeneous 1 := linearCoordinate_homogeneous _ j
  have hxell : ell.eval₂ (algebraMap K (DualNumber K)) x = 1 := by
    change aeval (R := K) x (linearCoordinate (basisCoordinateMatrix b) j) = 1
    rw [linearCoordinate_aeval]
    exact hOne
  have he : ∀ p ∈ (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)).toIdeal,
      p.eval₂ (algebraMap K (DualNumber K)) x = 0 := by
    intro p hp
    simp [show p = 0 from Ideal.mem_bot.mp hp]
  have hui : (↑(u⁻¹) : DualNumber K) = x i := by simp [x, tangentDualPoint, hdiag]
  have hBack : (fun s => (↑((u⁻¹)⁻¹) : DualNumber K) * x s) = tangentDualPoint U i := by
    funext s
    simp [x, ← mul_assoc]
  have hSource : linearNormalizedPoint ⊥ x ell hell hxell he ≫ quotientProjMap ⊥ =
      ambientNormalizedCoordinateChartPoint (F := K) (tangentDualPoint U i) i
        (by simp [tangentDualPoint, hdiag]) := by
    have h := linearNormalizedPoint_toAmbient_eq_unit_coordinateChartPoint ⊥ x ell hell hxell
      he i u⁻¹ hui
    simpa only [hBack] using h
  have hSquare := actual_linear_frame_normalized_point_square (basisCoordinateMatrix b)
    (basisCoordinateMatrix_isUnit b) x j hOne
  dsimp only at hSquare
  rw [hSource] at hSquare
  have hVector := funext hCoords
  simpa only [hVector] using hSquare

end PfaffianDescent.QuarticNet

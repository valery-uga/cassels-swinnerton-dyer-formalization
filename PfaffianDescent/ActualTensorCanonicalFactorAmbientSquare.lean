import PfaffianDescent.ProductDualOriginalComponentPresentations
import PfaffianDescent.ActualQuarticDualTensorCoordinates
import PfaffianDescent.FramedDualCommonChartCoordinates
import PfaffianDescent.AmbientNormalizedChartAlgebraNaturality
import PfaffianDescent.DualNumberPointSupport

/-! SOURCE ONLY, UNVERIFIED. The canonical factor presentation is computed
from the SAME actual eA/x/b/v tensor evaluator. The actual ambient square is
derived, including the diagonal unit normalization and all nilpotents. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
attribute [local instance] MvPolynomial.gradedAlgebra

def actualTensorProductDualCoordinates
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K)) :
    Fin 4 → FourTangentDualAlgebra K :=
  fun m => actualQuarticDualTensorEquiv eA b full ((1 : K) ⊗ₜ[k] x m)

theorem actualTensorProductDualCoordinates_one
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K))
    (j : Fin 4) (hxj : x j = 1) :
    actualTensorProductDualCoordinates eA x b full j = 1 := by
  unfold actualTensorProductDualCoordinates
  rw [tensor_coordinate_eq_one x j hxj, map_one]

def actualTensorProductDualOriginalAmbient
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K))
    (j : Fin 4) (hxj : x j = 1) :
    Spec (.of (FourTangentDualAlgebra K)) ⟶ Proj (homogeneousSubmodule (Fin 4) K) :=
  ambientNormalizedCoordinateChartPoint (F := K)
    (actualTensorProductDualCoordinates eA x b full) j
    (actualTensorProductDualCoordinates_one eA x b full j hxj)

theorem actualTensorProductDualOriginalAmbient_toBase
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K))
    (j : Fin 4) (hxj : x j = 1) :
    actualTensorProductDualOriginalAmbient eA x b full j hxj ≫ ambientToBase =
      actualProductDualToBase :=
  ambientNormalizedCoordinateChartPoint_toBase _ _ _

theorem actualDual_normalized_chart_conjugate_basis_one
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ m, eA (x m) = inl (b m) + inr (v m))
    (full : Fin 4 ≃ (L →ₐ[k] K)) (j : Fin 4) (hxj : x j = 1) (r : Fin 4) :
    conjugateBasis full b (conjugate_basis_span b full) r j = 1 := by
  have hb : b j = 1 := by
    have h := congrArg TrivSqZeroExt.fst (hx j)
    simpa only [hxj, map_one, TrivSqZeroExt.fst_one, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero] using h.symm
  rw [conjugateBasis_apply, hb, map_one]

theorem actualDual_framed_common_chart_eq
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ m, eA (x m) = inl (b m) + inr (v m))
    (full : Fin 4 ≃ (L →ₐ[k] K)) (j : Fin 4) (hxj : x j = 1) (r m : Fin 4) :
    framedDualCommonChart (conjugateBasis full b (conjugate_basis_span b full))
      (conjugateTangentMatrix full b v (conjugate_basis_span b full)) r j
      (by rw [actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj];
          exact one_ne_zero) m = dualNumberEmbedding (full r) (eA (x m)) := by
  let hs := conjugate_basis_span b full
  let cb := conjugateBasis full b hs
  let U := conjugateTangentMatrix full b v hs
  let c : DualNumber K := 1 + inr (-conjugateTangentRow full b v hs r r)
  have hc : cb r j ≠ 0 := by
    rw [actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj]
    exact one_ne_zero
  have hRaw (s : Fin 4) : framedDualRaw cb U r s =
      c * dualNumberEmbedding (full r) (eA (x s)) := by
    exact actualDual_conjugate_tangent_coordinates eA x b v hx full hs r s
  have hUnit : (framedDualChartUnit cb U r j hc : DualNumber K) = c := by
    rw [← framedDualRaw_chart_eq_unit, hRaw j, hxj, map_one, map_one, mul_one]
  change (↑((framedDualChartUnit cb U r j hc)⁻¹) : DualNumber K) *
    framedDualRaw cb U r m = _
  rw [hRaw m, ← hUnit, ← mul_assoc, Units.inv_mul, one_mul]

theorem actualTensorProductDual_factor_original_ambient_square
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ m, eA (x m) = inl (b m) + inr (v m))
    (full : Fin 4 ≃ (L →ₐ[k] K)) (j : Fin 4) (hxj : x j = 1) (r : Fin 4) :
    actualProductDualFactor r ≫ actualTensorProductDualOriginalAmbient eA x b full j hxj =
      ambientNormalizedCoordinateChartPoint (F := K)
        (tangentDualPoint (conjugateTangentMatrix full b v (conjugate_basis_span b full)) r)
        r (by simp [tangentDualPoint, conjugateTangentMatrix_diagonal]) ≫
      (linearCoordinateChangeAmbientIso
        (basisCoordinateMatrix (conjugateBasis full b (conjugate_basis_span b full)))
        (basisCoordinateMatrix_isUnit _)).inv := by
  let hs := conjugate_basis_span b full
  let cb := conjugateBasis full b hs
  let U := conjugateTangentMatrix full b v hs
  have hc : cb r j ≠ 0 := by
    rw [actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj]
    exact one_ne_zero
  have hRows : (fun m => actualTensorProductDualCoordinates eA x b full m r) =
      framedDualCommonChart cb U r j hc := by
    funext m
    rw [actualDual_framed_common_chart_eq eA x b v hx full j hxj r m]
    simp only [actualTensorProductDualCoordinates, actualQuarticDualTensorEquiv_tmul,
      one_mul, dualNumberEmbedding_apply]
  have hFactor := ambientNormalizedCoordinateChartPoint_algHom
    (Pi.evalAlgHom K (fun _ : Fin 4 => DualNumber K) r)
    (actualTensorProductDualCoordinates eA x b full) j
    (actualTensorProductDualCoordinates_one eA x b full j hxj)
  have hEval : (Pi.evalAlgHom K (fun _ : Fin 4 => DualNumber K) r).toRingHom =
      Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) r := rfl
  rw [hEval] at hFactor
  simp only [Pi.evalAlgHom_apply, hRows] at hFactor
  have hFactorActual :
      actualProductDualFactor r ≫ actualTensorProductDualOriginalAmbient eA x b full j hxj =
        ambientNormalizedCoordinateChartPoint (F := K)
          (framedDualCommonChart cb U r j hc) j (framedDualCommonChart_one cb U r j hc) := by
    simpa only [actualProductDualFactor, actualTensorProductDualOriginalAmbient,
      Pi.coe_evalAlgHom] using hFactor.symm
  exact hFactorActual.trans (framedDual_common_chart_actual_square cb U
    (conjugateTangentMatrix_diagonal full b v hs) r j hc).symm

theorem actualTensorProductDual_factor_actual_support_point
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ m, eA (x m) = inl (b m) + inr (v m))
    (full : Fin 4 ≃ (L →ₐ[k] K)) (j : Fin 4) (hxj : x j = 1) (r : Fin 4) :
    (actualProductDualFactor r ≫ actualTensorProductDualOriginalAmbient eA x b full j hxj)
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
        (IsLocalRing.closedPoint K)) =
      ambientNormalizedCoordinateChartPoint (F := K)
        (conjugateBasis full b (conjugate_basis_span b full) r) j
        (actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj r)
        (IsLocalRing.closedPoint K) := by
  let Y := actualTensorProductDualCoordinates eA x b full
  have hRow := ambientNormalizedCoordinateChartPoint_algHom
    (Pi.evalAlgHom K (fun _ : Fin 4 => DualNumber K) r) Y j
    (actualTensorProductDualCoordinates_one eA x b full j hxj)
  have hEval : (Pi.evalAlgHom K (fun _ : Fin 4 => DualNumber K) r).toRingHom =
      Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) r := rfl
  rw [hEval] at hRow
  have hRed := ambientNormalizedCoordinateChartPoint_algHom
    (TrivSqZeroExt.fstHom K K K) (fun m => Y m r) j
    (by simp [Y, actualTensorProductDualCoordinates_one eA x b full j hxj])
  have hCoeffs : (fun m => (Y m r).fst) =
      conjugateBasis full b (conjugate_basis_span b full) r := by
    funext m
    simp only [Y, actualTensorProductDualCoordinates, actualQuarticDualTensorEquiv_tmul,
      one_mul, hx, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero, conjugateBasis_apply]
    rfl
  simp only [TrivSqZeroExt.fstHom_apply, hCoeffs] at hRed
  have hRowActual :
      actualProductDualFactor r ≫ actualTensorProductDualOriginalAmbient eA x b full j hxj =
        ambientNormalizedCoordinateChartPoint (F := K) (fun m => Y m r) j
          (by simp [Y, actualTensorProductDualCoordinates_one eA x b full j hxj]) := by
    simpa only [actualProductDualFactor, actualTensorProductDualOriginalAmbient,
      Pi.coe_evalAlgHom, Pi.evalAlgHom_apply, Y] using hRow.symm
  have hMaps : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫
      actualProductDualFactor r ≫ actualTensorProductDualOriginalAmbient eA x b full j hxj =
      ambientNormalizedCoordinateChartPoint (F := K)
        (conjugateBasis full b (conjugate_basis_span b full) r) j
        (actualDual_normalized_chart_conjugate_basis_one eA x b v hx full j hxj r) := by
    exact (congrArg (fun f =>
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ f)
      hRowActual).trans hRed.symm
  exact congrArg (fun f => f (IsLocalRing.closedPoint K)) hMaps

end PfaffianDescent.QuarticNet

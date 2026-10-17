import PfaffianDescent.FramedDualCommonChartCoordinates
import PfaffianDescent.ActualDualAlgebraConjugateTangentCoordinates
import PfaffianDescent.FourTangentDualRescaleScheme
import PfaffianDescent.AmbientNormalizedChartAlgebraNaturality

/-! SOURCE ONLY, UNVERIFIED. The actual dual algebra coordinate identity
implies a projective morphism identity, including the epsilon parameter.
The original algebra, coordinate evaluator and conjugate frame are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual normalized chart vector is recovered by cancelling the
explicit projective diagonal unit, rather than discarding nilpotents. -/
theorem actualConjugate_framedDualCommonChart_zero
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = inl (b r) + inr (v r))
    (hx0 : x 0 = 1) (hb0 : b 0 = 1)
    (full : Fin 4 ≃ (L →ₐ[k] K))
    (hs : Submodule.span K
      (Set.range (fun sigma : L →ₐ[k] K => fun r => sigma (b r))) = ⊤)
    (row : Fin 4) :
    framedDualCommonChart (conjugateBasis full b hs)
      (conjugateTangentMatrix full b v hs) row 0
      (by rw [conjugateBasis_apply, hb0, map_one]; exact one_ne_zero) =
      fun m => dualNumberEmbedding (full row) (eA (x m)) := by
  let B := conjugateBasis full b hs
  let U := conjugateTangentMatrix full b v hs
  let c : DualNumber K := 1 + inr (-conjugateTangentRow full b v hs row row)
  let Y : Fin 4 → DualNumber K := fun m => dualNumberEmbedding (full row) (eA (x m))
  have hc : B row 0 ≠ 0 := by
    rw [conjugateBasis_apply, hb0, map_one]
    exact one_ne_zero
  let u := framedDualChartUnit B U row 0 hc
  have hRaw (m : Fin 4) : framedDualRaw B U row m = c * Y m := by
    simpa only [framedDualRaw, B, U, c, Y, basisCoordinateMatrix] using
      actualDual_conjugate_tangent_coordinates eA x b v hx full hs row m
  have hY0 : Y 0 = 1 := by simp only [Y, hx0, map_one]
  have hu : (u : DualNumber K) = c := by
    calc
      (u : DualNumber K) = framedDualRaw B U row 0 :=
        (framedDualRaw_chart_eq_unit B U row 0 hc).symm
      _ = c * Y 0 := hRaw 0
      _ = c := by rw [hY0, mul_one]
  funext m
  change (↑(u⁻¹) : DualNumber K) * framedDualRaw B U row m = Y m
  rw [hRaw, ← hu, ← mul_assoc, Units.inv_mul, one_mul]

/-- Exact actual GL square before row rescaling. The inverse ambient frame
map corresponds to polynomial substitution by the conjugate-basis matrix. -/
theorem actualConjugate_dualComponent_frame_square
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = inl (b r) + inr (v r))
    (hx0 : x 0 = 1) (hb0 : b 0 = 1)
    (full : Fin 4 ≃ (L →ₐ[k] K))
    (hs : Submodule.span K
      (Set.range (fun sigma : L →ₐ[k] K => fun r => sigma (b r))) = ⊤)
    (row : Fin 4) :
    ambientNormalizedCoordinateChartPoint (F := K)
      (tangentDualPoint (conjugateTangentMatrix full b v hs) row) row
      (by simp [tangentDualPoint, conjugateTangentMatrix_diagonal]) ≫
        (linearCoordinateChangeAmbientIso
          (basisCoordinateMatrix (conjugateBasis full b hs))
          (basisCoordinateMatrix_isUnit _)).inv =
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun m => dualNumberEmbedding (full row) (eA (x m))) 0
        (by rw [hx0, map_one, map_one]) := by
  have h := framedDual_common_chart_actual_square (conjugateBasis full b hs)
    (conjugateTangentMatrix full b v hs)
    (conjugateTangentMatrix_diagonal full b v hs) row 0
    (by rw [conjugateBasis_apply, hb0, map_one]; exact one_ne_zero)
  simpa only [actualConjugate_framedDualCommonChart_zero eA x b v hx hx0 hb0 full hs row]
    using h

/-- Nonzero row rescaling is the actual dual-number automorphism on the SAME
component source, and the GL square follows by morphism composition. -/
theorem actualConjugate_rescaled_dualComponent_frame_square
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = inl (b r) + inr (v r))
    (hx0 : x 0 = 1) (hb0 : b 0 = 1)
    (full : Fin 4 ≃ (L →ₐ[k] K))
    (hs : Submodule.span K
      (Set.range (fun sigma : L →ₐ[k] K => fun r => sigma (b r))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ row, l row ≠ 0) (row : Fin 4) :
    ambientNormalizedCoordinateChartPoint (F := K)
      (tangentDualPoint (rescaleTangentDirections l
        (conjugateTangentMatrix full b v hs)) row) row
      (by simp [tangentDualPoint, rescaleTangentDirections,
        conjugateTangentMatrix_diagonal]) ≫
        (linearCoordinateChangeAmbientIso
          (basisCoordinateMatrix (conjugateBasis full b hs))
          (basisCoordinateMatrix_isUnit _)).inv =
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun m => dualNumberRescale (l row)
          (dualNumberEmbedding (full row) (eA (x m)))) 0
        (by rw [hx0, map_one, map_one, map_one]) := by
  let U := conjugateTangentMatrix full b v hs
  let phi := (dualNumberRescaleEquiv (l row) (hl row)).toAlgHom
  have hcoords : (fun m => phi (tangentDualPoint U row m)) =
      tangentDualPoint (rescaleTangentDirections l U) row := by
    funext m
    change dualNumberRescale (l row) (tangentDualPoint U row m) =
      tangentDualPoint (rescaleTangentDirections l U) row m
    apply TrivSqZeroExt.ext <;>
      simp [dualNumberRescale, tangentDualPoint, rescaleTangentDirections,
        TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, mul_comm]
  have h := ambientNormalizedCoordinateChartPoint_algHom phi
    (tangentDualPoint U row) row
    (by simp [U, tangentDualPoint, conjugateTangentMatrix_diagonal])
  simp only [hcoords] at h
  rw [h, Category.assoc,
    actualConjugate_dualComponent_frame_square eA x b v hx hx0 hb0 full hs row]
  exact (ambientNormalizedCoordinateChartPoint_algHom phi
    (fun m => dualNumberEmbedding (full row) (eA (x m))) 0
    (by rw [hx0, map_one, map_one])).symm

end PfaffianDescent.QuarticNet

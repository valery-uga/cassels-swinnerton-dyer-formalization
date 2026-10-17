import PfaffianDescent.ActualConjugateDualFrameSchemeSquare
import PfaffianDescent.ActualQuarticTensorRescaledSchemeCoordinates
import PfaffianDescent.SingleSupportGeometricSchemeSplitting
import PfaffianDescent.AmbientProjectiveRenameChartSquare

/-! SOURCE ONLY, UNVERIFIED. Actual base-change/product-dual Iso and actual
component square, with the original selected chart permutation retained. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The true original field base change, followed by the embedding-indexed
and epsilon-rescaled tensor equivalence. No source comparison is supplied. -/
def actualRescaledQuarticSchemeIso
    {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (eA : letI := finiteSchemeCoefficientAlgebra t
      Γ(Z, ⊤) ≃ₐ[k] DualNumber L)
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K))
    (l : Fin 4 → K) (hl : ∀ row, l row ≠ 0) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) t ≅
      Spec (.of (FourTangentDualAlgebra K)) := by
  letI := finiteSchemeCoefficientAlgebra t
  exact finiteSchemeActualFieldBaseChangeIso (K := K) t ≪≫
    actualQuarticDualTensorRescaledSpecIso eA b full l hl

/-- Every actual dual component has the required GL square. The matrix is
built from the actual residue basis. The source Iso retains the SAME Z. -/
theorem actualRescaledQuarticSchemeIso_component_frame_square
    {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (eA : letI := finiteSchemeCoefficientAlgebra t
      Γ(Z, ⊤) ≃ₐ[k] DualNumber L)
    (x : Fin 4 → Γ(Z, ⊤)) (j : Fin 4) (hxj : x j = 1)
    (pi : Equiv.Perm (Fin 4)) (hpi : pi 0 = j)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x (pi r)) = inl (b r) + inr (v r))
    (hb0 : b 0 = 1) (full : Fin 4 ≃ (L →ₐ[k] K))
    (hs : Submodule.span K
      (Set.range (fun sigma : L →ₐ[k] K => fun r => sigma (b r))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ row, l row ≠ 0) :
    letI := finiteSchemeCoefficientAlgebra t
    let S := actualRescaledQuarticSchemeIso t eA b full l hl
    let Q := (finiteSchemeActualFieldBaseChangeIso (K := K) t).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
    ∀ row, Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) row)) ≫
        S.inv ≫ Q ≫ ambientProjectiveRenameMap (K := K) pi =
      ambientNormalizedCoordinateChartPoint (F := K)
        (tangentDualPoint (rescaleTangentDirections l
          (conjugateTangentMatrix full b v hs)) row) row
        (by simp [tangentDualPoint, rescaleTangentDirections,
          conjugateTangentMatrix_diagonal]) ≫
        (linearCoordinateChangeAmbientIso
          (basisCoordinateMatrix (conjugateBasis full b hs))
          (basisCoordinateMatrix_isUnit _)).inv := by
  letI := finiteSchemeCoefficientAlgebra t
  dsimp only
  intro row
  let eT := finiteSchemeActualFieldBaseChangeIso (K := K) t
  let theta := actualQuarticDualTensorRescaledEquiv eA b full l hl
  let thetaS := actualQuarticDualTensorRescaledSpecIso eA b full l hl
  let ev := Pi.evalAlgHom K (fun _ : Fin 4 => DualNumber K) row
  let phi := ev.comp theta.toAlgHom
  let y : Fin 4 → K ⊗[k] Γ(Z, ⊤) := fun r => (1 : K) ⊗ₜ[k] x r
  have hyj : y j = 1 := tensor_coordinate_eq_one x j hxj
  have hSpec : Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ thetaS.inv =
      Spec.map (CommRingCat.ofHom phi.toRingHom) := by
    rw [actualQuarticDualTensorRescaledSpecIso_inv, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl
  have hCoords : (fun m => phi (y (pi m))) =
      fun m => dualNumberRescale (l row)
        (dualNumberEmbedding (full row) (eA (x (pi m)))) := by
    funext m
    change theta ((1 : K) ⊗ₜ[k] x (pi m)) row = _
    rw [actualQuarticDualTensorRescaledEquiv_tmul]
    apply TrivSqZeroExt.ext <;>
      simp [dualNumberEmbedding, dualNumberRescale,
        TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]
  have hPoint : Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
      ambientNormalizedCoordinateChartPoint (F := K) (fun m => y (pi m)) 0
        (by rw [hpi]; exact hyj) =
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun m => dualNumberRescale (l row)
          (dualNumberEmbedding (full row) (eA (x (pi m))))) 0
        (by rw [hpi, hxj, map_one, map_one, map_one]) := by
    have h := ambientNormalizedCoordinateChartPoint_algHom phi
      (fun m => y (pi m)) 0 (by rw [hpi]; exact hyj)
    simpa only [hCoords] using h.symm
  change Spec.map (CommRingCat.ofHom ev.toRingHom) ≫
    (eT ≪≫ thetaS).inv ≫ (eT.hom ≫
      ambientNormalizedCoordinateChartPoint (F := K) y j hyj) ≫
        ambientProjectiveRenameMap (K := K) pi = _
  simp only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom ev.toRingHom)), hSpec]
  rw [ambientNormalizedCoordinateChartPoint_rename_zero y j hyj pi hpi, hPoint]
  exact (actualConjugate_rescaled_dualComponent_frame_square eA
    (fun r => x (pi r)) b v hx (by rw [hpi]; exact hxj) hb0
    full hs l hl row).symm

end PfaffianDescent.QuarticNet

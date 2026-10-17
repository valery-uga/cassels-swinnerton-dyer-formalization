import PfaffianDescent.ActualTensorCanonicalFactorAmbientSquare
import PfaffianDescent.SingleSupportGeometricSchemeSplitting
import PfaffianDescent.FourTangentDualRescaleScheme

/-! SOURCE ONLY, UNVERIFIED. Actual four-component presentation of the
original field base change, in its original ambient coordinate order.
Nonzero skew weights are literal source automorphisms of the dual factors.
No supplied component, frame, or desired embedding comparison is an input. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalOrderQuarticSchemeIso
    {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (eA : letI := finiteSchemeCoefficientAlgebra t
      Γ(Z, ⊤) ≃ₐ[k] DualNumber L)
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K)) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) t ≅
      Spec (.of (FourTangentDualAlgebra K)) := by
  letI := finiteSchemeCoefficientAlgebra t
  exact finiteSchemeActualFieldBaseChangeIso (K := K) t ≪≫
    Scheme.Spec.mapIso (actualQuarticDualTensorEquiv eA b full).toRingEquiv.toCommRingCatIso.symm.op

theorem actualOriginalOrderQuarticSchemeIso_original_ambient_square
    {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (eA : letI := finiteSchemeCoefficientAlgebra t
      Γ(Z, ⊤) ≃ₐ[k] DualNumber L)
    (x : Fin 4 → Γ(Z, ⊤)) (j : Fin 4) (hxj : x j = 1)
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K)) :
    letI := finiteSchemeCoefficientAlgebra t
    let S := actualOriginalOrderQuarticSchemeIso t eA b full
    let Q := (finiteSchemeActualFieldBaseChangeIso (K := K) t).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
    S.inv ≫ Q = actualTensorProductDualOriginalAmbient eA x b full j hxj := by
  letI := finiteSchemeCoefficientAlgebra t
  dsimp only
  simp only [actualOriginalOrderQuarticSchemeIso, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact (ambientNormalizedCoordinateChartPoint_algHom
    (actualQuarticDualTensorEquiv eA b full).toAlgHom
    (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)).symm

theorem actualOriginalOrderQuarticSchemeIso_component_frame_square
    {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (eA : letI := finiteSchemeCoefficientAlgebra t
      Γ(Z, ⊤) ≃ₐ[k] DualNumber L)
    (x : Fin 4 → Γ(Z, ⊤)) (j : Fin 4) (hxj : x j = 1)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : letI := finiteSchemeCoefficientAlgebra t
      ∀ m, eA (x m) = inl (b m) + inr (v m))
    (full : Fin 4 ≃ (L →ₐ[k] K)) :
    letI := finiteSchemeCoefficientAlgebra t
    let S := actualOriginalOrderQuarticSchemeIso t eA b full
    let Q := (finiteSchemeActualFieldBaseChangeIso (K := K) t).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
    let U := conjugateTangentMatrix full b v (conjugate_basis_span b full)
    let B := conjugateBasis full b (conjugate_basis_span b full)
    ∀ r, actualProductDualFactor r ≫ S.inv ≫ Q =
      ambientNormalizedCoordinateChartPoint (F := K) (tangentDualPoint U r) r
        (by simp [U, tangentDualPoint, conjugateTangentMatrix_diagonal]) ≫
      (linearCoordinateChangeAmbientIso (basisCoordinateMatrix B)
        (basisCoordinateMatrix_isUnit B)).inv := by
  letI := finiteSchemeCoefficientAlgebra t
  dsimp only
  intro r
  rw [actualOriginalOrderQuarticSchemeIso_original_ambient_square t eA x j hxj b full]
  exact actualTensorProductDual_factor_original_ambient_square eA x b v hx full j hxj r

theorem actualOriginalOrderQuarticSchemeIso_rescaled_component_frame_square
    {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t]
    (eA : letI := finiteSchemeCoefficientAlgebra t
      Γ(Z, ⊤) ≃ₐ[k] DualNumber L)
    (x : Fin 4 → Γ(Z, ⊤)) (j : Fin 4) (hxj : x j = 1)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : letI := finiteSchemeCoefficientAlgebra t
      ∀ m, eA (x m) = inl (b m) + inr (v m))
    (full : Fin 4 ≃ (L →ₐ[k] K))
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) :
    letI := finiteSchemeCoefficientAlgebra t
    let S := actualOriginalOrderQuarticSchemeIso t eA b full
    let Q := (finiteSchemeActualFieldBaseChangeIso (K := K) t).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
    let U := rescaleTangentDirections l
      (conjugateTangentMatrix full b v (conjugate_basis_span b full))
    let B := conjugateBasis full b (conjugate_basis_span b full)
    ∀ r, Spec.map (CommRingCat.ofHom (dualNumberRescaleEquiv (l r) (hl r)).toRingHom) ≫
      actualProductDualFactor r ≫ S.inv ≫ Q =
      ambientNormalizedCoordinateChartPoint (F := K) (tangentDualPoint U r) r
        (by simp [U, tangentDualPoint, rescaleTangentDirections,
          conjugateTangentMatrix_diagonal]) ≫
      (linearCoordinateChangeAmbientIso (basisCoordinateMatrix B)
        (basisCoordinateMatrix_isUnit B)).inv := by
  letI := finiteSchemeCoefficientAlgebra t
  dsimp only
  intro r
  let U0 := conjugateTangentMatrix full b v (conjugate_basis_span b full)
  let phi := (dualNumberRescaleEquiv (l r) (hl r)).toAlgHom
  have hcoords : (fun m => phi (tangentDualPoint U0 r m)) =
      tangentDualPoint (rescaleTangentDirections l U0) r := by
    funext m
    change dualNumberRescale (l r) (tangentDualPoint U0 r m) =
      tangentDualPoint (rescaleTangentDirections l U0) r m
    apply TrivSqZeroExt.ext <;>
      simp [dualNumberRescale, tangentDualPoint, rescaleTangentDirections,
        TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, mul_comm]
  have hNatural := ambientNormalizedCoordinateChartPoint_algHom phi
    (tangentDualPoint U0 r) r
    (by simp [U0, tangentDualPoint, conjugateTangentMatrix_diagonal])
  simp only [hcoords] at hNatural
  rw [actualOriginalOrderQuarticSchemeIso_component_frame_square t eA x j hxj b v hx full r]
  rw [← Category.assoc, ← hNatural]

end PfaffianDescent.QuarticNet

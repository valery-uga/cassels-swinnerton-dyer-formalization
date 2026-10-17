import PfaffianDescent.QuarticEmbeddingIndexedTensor
import PfaffianDescent.QuarticGeometricSplitting
import PfaffianDescent.ActualDualAlgebraConjugateTangentCoordinates
import PfaffianDescent.QuarticTangentRescalingExactKernel
import PfaffianDescent.FourTangentDualCoordinates

/-! Exact full-coefficient equation transport for the actual scalar-extended
supplied algebra. The tensor isomorphism is indexed by the SAME embeddings
as its tangent matrix; all extension-field homogeneous equations, including
nilpotent conditions, are retained. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial Module TrivSqZeroExt
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]

private def dualNumberFourPi (K : Type u) [Field K] :
    DualNumber (Fin 4 → K) ≃ₐ[K] (Fin 4 → DualNumber K) where
  toFun x i := (x.fst i, x.snd i)
  invFun f := (fun i => (f i).fst, fun i => (f i).snd)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Canonical embedding-indexed decomposition of the actual scalar extension
of A, using its own dual presentation. No abstract splitting is substituted. -/
def actualQuarticDualTensorEquiv
    (eA : A ≃ₐ[k] DualNumber L) (b : Basis (Fin 4) k L)
    (full : Fin 4 ≃ (L →ₐ[k] K)) :
    (K ⊗[k] A) ≃ₐ[K] FourTangentDualAlgebra K :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) eA).trans
    ((dualNumberBaseChange k K L).trans
      ((dualNumberCongr (quarticEmbeddingTensorEquiv b full)).trans
        (dualNumberFourPi K)))

private theorem dualNumberBaseChange_tmul (c : K) (z : DualNumber L) :
    dualNumberBaseChange k K L (c ⊗ₜ[k] z) =
      (c ⊗ₜ[k] z.fst, c ⊗ₜ[k] z.snd) := rfl

/-- Exact images of actual original-algebra elements in each dual factor. -/
@[simp] theorem actualQuarticDualTensorEquiv_tmul
    (eA : A ≃ₐ[k] DualNumber L) (b : Basis (Fin 4) k L)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (c : K) (a : A) (i : Fin 4) :
    actualQuarticDualTensorEquiv eA b full (c ⊗ₜ[k] a) i =
      (c * full i (eA a).fst, c * full i (eA a).snd) := by
  have ht : actualQuarticDualTensorEquiv eA b full (c ⊗ₜ[k] a) i =
      dualNumberFourPi K
        (dualNumberCongr (quarticEmbeddingTensorEquiv b full)
          (c ⊗ₜ[k] (eA a).fst, c ⊗ₜ[k] (eA a).snd)) i := rfl
  rw [ht]
  have hcongr (z : DualNumber (K ⊗[k] L)) :
      dualNumberCongr (quarticEmbeddingTensorEquiv b full) z =
      TrivSqZeroExt.inl (quarticEmbeddingTensorEquiv b full z.fst) +
        TrivSqZeroExt.inr (quarticEmbeddingTensorEquiv b full z.snd) := rfl
  have hpi (z : DualNumber (Fin 4 → K)) :
      dualNumberFourPi K z i = (z.fst i, z.snd i) := rfl
  rw [hcongr, hpi]
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_inr, add_zero, zero_add]
  change (quarticEmbeddingTensorEquiv b full (c ⊗ₜ[k] (eA a).fst) i,
    quarticEmbeddingTensorEquiv b full (c ⊗ₜ[k] (eA a).snd) i) = _
  simp only [quarticEmbeddingTensorEquiv_tmul]

/-- Every K-coefficient homogeneous equation is transported, not merely
those obtained by mapping an individual ground-field polynomial. -/
theorem actualQuarticTensor_homogeneous_equation_iff
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (full : Fin 4 ≃ (L →ₐ[k] K))
    (F : MvPolynomial (Fin 4) K) (n : ℕ) (hF : F.IsHomogeneous n) :
    let hs := conjugate_basis_span b full
    let U := conjugateTangentMatrix full b v hs
    let M := basisCoordinateMatrix (conjugateBasis full b hs)
    aeval (R := K) (fourTangentRawCoordinates U) (linearSubstitution M F) = 0 ↔
      aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] x r) F = 0 := by
  let hs := conjugate_basis_span b full
  let U := conjugateTangentMatrix full b v hs
  let M := basisCoordinateMatrix (conjugateBasis full b hs)
  let theta := actualQuarticDualTensorEquiv eA b full
  let y : Fin 4 → K ⊗[k] A := fun r => (1 : K) ⊗ₜ[k] x r
  let Y : Fin 4 → FourTangentDualAlgebra K := fun r => theta (y r)
  let c : FourTangentDualAlgebra K := fun row =>
    1 + TrivSqZeroExt.inr (-conjugateTangentRow full b v hs row row)
  have hY (r row : Fin 4) : Y r row =
      dualNumberEmbedding (full row) (eA (x r)) := by
    simpa only [Y, y, theta, actualQuarticDualTensorEquiv_tmul, one_mul,
      dualNumberEmbedding_apply] using (rfl :
      ((full row) (eA (x r)).fst, (full row) (eA (x r)).snd) =
      ((full row) (eA (x r)).fst, (full row) (eA (x r)).snd))
  have hcoordinates : (fun m => ∑ r,
      algebraMap K (FourTangentDualAlgebra K) (M m r) * fourTangentRawCoordinates U r) = (fun m => c * Y m) := by
    funext m row
    have h := actualDual_conjugate_tangent_coordinates eA x b v hx full hs row m
    simpa only [M, U, c, Finset.sum_apply, Pi.mul_apply,
      fourTangentRawCoordinates, Pi.algebraMap_apply, hY] using h
  have hunit : IsUnit c := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨(fun row => 1 + TrivSqZeroExt.inr
      (conjugateTangentRow full b v hs row row)), ?_⟩
    funext row
    apply TrivSqZeroExt.ext <;> simp [c, DualNumber.snd_mul]
  have hYeval : aeval (R := K) Y F = theta (aeval (R := K) y F) :=
    (comp_aeval_apply y theta.toAlgHom F).symm
  change aeval (R := K) (fourTangentRawCoordinates U) (linearSubstitution M F) = 0 ↔
    aeval (R := K) y F = 0
  have heval : aeval (R := K) (fun m => c * Y m) F =
      c ^ n * aeval (R := K) Y F :=
    AllCharacteristics.eval₂_homogeneous_smul F hF
      (algebraMap K (FourTangentDualAlgebra K)) Y c
  rw [aeval_linearSubstitution, hcoordinates, heval, hYeval]
  constructor
  · intro hz
    have htheta : theta (aeval (R := K) y F) = 0 :=
      (hunit.pow n).mul_left_cancel (by simpa using hz)
    exact theta.injective (by simpa using htheta)
  · intro hz
    simp [hz]

/-- The same exact comparison after BOTH normalizations: nonzero skew row
rescaling and the common sum-of-coordinates chart of the four double points. -/
theorem actualQuarticTensor_normalized_rescaled_equation_iff
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ row, l row ≠ 0)
    (F : MvPolynomial (Fin 4) K) (n : ℕ) (hF : F.IsHomogeneous n) :
    let hs := conjugate_basis_span b full
    let U := conjugateTangentMatrix full b v hs
    let M := basisCoordinateMatrix (conjugateBasis full b hs)
    aeval (R := K) (fourTangentNormalizedCoordinates (rescaleTangentDirections l U))
      (linearSubstitution M F) = 0 ↔
      aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] x r) F = 0 := by
  let hs := conjugate_basis_span b full
  let U := conjugateTangentMatrix full b v hs
  let M := basisCoordinateMatrix (conjugateBasis full b hs)
  let G := linearSubstitution M F
  have hG : G.IsHomogeneous n := linearSubstitution_homogeneous M hF
  change aeval (R := K) (fourTangentNormalizedCoordinates (rescaleTangentDirections l U)) G = 0 ↔ _
  rw [fourTangentNormalized_eval_zero_iff _ G hG]
  have hscale : (∀ row, aeval (R := K) (tangentDualPoint (rescaleTangentDirections l U) row) G = 0) ↔
      ∀ row, aeval (R := K) (tangentDualPoint U row) G = 0 :=
    forall_congr' (fun row => rescaleTangentDirections_equation_iff U l hl G row)
  rw [hscale]
  have hraw : aeval (R := K) (fourTangentRawCoordinates U) G = 0 ↔
      ∀ row, aeval (R := K) (tangentDualPoint U row) G = 0 := by
    constructor
    · intro hz row
      simpa only [fourTangentRawEvaluation_apply, Pi.zero_apply] using congrFun hz row
    · intro hz
      funext row
      exact (fourTangentRawEvaluation_apply U G row).trans (hz row)
  rw [← hraw]
  exact actualQuarticTensor_homogeneous_equation_iff eA x b v hx full F n hF

end PfaffianDescent.QuarticNet

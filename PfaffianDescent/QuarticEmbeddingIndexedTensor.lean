import PfaffianDescent.QuarticConjugateSpan
import PfaffianDescent.QuarticConjugateJets
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps

/-! The actual embedding-indexed scalar-extension algebra of a quartic
residue field. Bijectivity is derived from its actual basis/discriminant;
no tensor-coordinate comparison or range certificate is supplied. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
open scoped TensorProduct
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]

/-- The canonical tensor evaluator indexed by the specified actual embeddings. -/
def quarticEmbeddingTensorMap (full : Fin 4 ≃ (L →ₐ[k] K)) :
    (K ⊗[k] L) →ₐ[K] (Fin 4 → K) :=
  Algebra.TensorProduct.lift (Algebra.ofId K (Fin 4 → K))
    (AlgHom.pi (fun i => full i)) (fun _ _ => Commute.all _ _)

@[simp] theorem quarticEmbeddingTensorMap_tmul
    (full : Fin 4 ≃ (L →ₐ[k] K)) (c : K) (z : L) (i : Fin 4) :
    quarticEmbeddingTensorMap full (c ⊗ₜ[k] z) i = c * full i z := rfl

/-- The actual residue basis proves this canonical evaluator bijective. -/
theorem quarticEmbeddingTensorMap_bijective
    [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K)) :
    Function.Bijective (quarticEmbeddingTensorMap full) := by
  classical
  letI : Module.Finite K (K ⊗[k] L) := Module.Finite.of_basis (b.baseChange K)
  let nu := quarticEmbeddingTensorMap full
  let cb := conjugateBasis full b (conjugate_basis_span b full)
  let M := basisCoordinateMatrix cb
  have hdet : M.det ≠ 0 := (basisCoordinateMatrix_isUnit cb).ne_zero
  have hLI : LinearIndependent K (fun j => M j) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  let B : Basis (Fin 4) K (Fin 4 → K) :=
    basisOfLinearIndependentOfCardEqFinrank hLI (by simp)
  have hspanM : Submodule.span K (Set.range (fun j => M j)) = ⊤ := by
    simpa [B] using B.span_eq
  have himage (j : Fin 4) : nu ((b.baseChange K) j) = M j := by
    funext i
    simp [nu, M, cb, basisCoordinateMatrix, conjugateBasis_apply]
  have hrange : LinearMap.range nu.toLinearMap = ⊤ := by
    apply top_unique
    rw [← hspanM]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨(b.baseChange K) j, himage j⟩
  have hsurj : Function.Surjective nu := LinearMap.range_eq_top.mp hrange
  have hdim : finrank K (K ⊗[k] L) = finrank K (Fin 4 → K) := by
    rw [Module.finrank_eq_card_basis (b.baseChange K)]
    simp
  have hinj : Function.Injective nu :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := nu.toLinearMap)).mpr hsurj
  exact ⟨hinj, hsurj⟩

/-- Its underlying map is the literal actual embedding evaluator above. -/
def quarticEmbeddingTensorEquiv
    [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K)) :
    (K ⊗[k] L) ≃ₐ[K] (Fin 4 → K) :=
  AlgEquiv.ofBijective (quarticEmbeddingTensorMap full)
    (quarticEmbeddingTensorMap_bijective b full)

@[simp] theorem quarticEmbeddingTensorEquiv_tmul
    [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (b : Basis (Fin 4) k L) (full : Fin 4 ≃ (L →ₐ[k] K))
    (c : K) (z : L) (i : Fin 4) :
    quarticEmbeddingTensorEquiv b full (c ⊗ₜ[k] z) i = c * full i z := rfl

end PfaffianDescent.QuarticNet

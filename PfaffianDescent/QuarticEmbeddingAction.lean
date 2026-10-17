import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Galois action on the four embeddings of a separable residue field
-/

namespace PfaffianDescent
namespace QuarticNet

variable {k L K : Type*} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]

noncomputable def embeddingAction (g : K ≃ₐ[k] K) :
    Equiv.Perm (L →ₐ[k] K) where
  toFun σ := g.toAlgHom.comp σ
  invFun σ := g.symm.toAlgHom.comp σ
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

theorem embeddingAction_transitive [Normal k K] (σ τ : L →ₐ[k] K) :
    ∃ g : K ≃ₐ[k] K, embeddingAction g σ = τ := by
  letI : Algebra L K := σ.toRingHom.toAlgebra
  letI : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq fun x =>
    (σ.commutes x).symm
  let f : K →ₐ[k] K := τ.liftNormal K
  let g : K ≃ₐ[k] K := AlgEquiv.ofBijective f (AlgHom.normal_bijective k K K f)
  refine ⟨g, ?_⟩
  ext x
  exact τ.liftNormal_commutes K x

noncomputable def indexedEmbeddingAction (e : Fin 4 ≃ (L →ₐ[k] K))
    (g : K ≃ₐ[k] K) : Equiv.Perm (Fin 4) :=
  e.trans ((embeddingAction g).trans e.symm)

theorem indexedEmbeddingAction_apply (e : Fin 4 ≃ (L →ₐ[k] K))
    (g : K ≃ₐ[k] K) (i : Fin 4) (x : L) :
    e (indexedEmbeddingAction e g i) x = g (e i x) := by
  simp [indexedEmbeddingAction, embeddingAction]

theorem indexedEmbeddingAction_transitive [Normal k K]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (i j : Fin 4) :
    ∃ g : K ≃ₐ[k] K, indexedEmbeddingAction e g i = j := by
  obtain ⟨g, hg⟩ := embeddingAction_transitive (e i) (e j)
  refine ⟨g, e.injective ?_⟩
  simpa [indexedEmbeddingAction] using hg

theorem exists_four_embeddings [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [IsAlgClosed K] (hL : Module.finrank k L = 4) :
    Nonempty (Fin 4 ≃ (L →ₐ[k] K)) := by
  classical
  apply Fintype.card_eq.mp
  simpa only [Fintype.card_fin, hL] using (AlgHom.card k L K).symm

end QuarticNet
end PfaffianDescent

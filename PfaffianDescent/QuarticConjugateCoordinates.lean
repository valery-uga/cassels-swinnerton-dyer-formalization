import PfaffianDescent.QuarticEmbeddingAction
import PfaffianDescent.PolynomialLinearChange
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Coordinates and tangent directions of the four conjugate points

The four embeddings of a separable quartic residue field provide a coordinate
basis after base change.  Expressing a tangent vector in that basis gives the
matrix of four tangent directions used in the degree-four argument.
-/

namespace PfaffianDescent
namespace QuarticNet

open Module

variable {k L K : Type*} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]

noncomputable def conjugateBasis (e : Fin 4 ≃ (L →ₐ[k] K)) (p : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤) :
    Basis (Fin 4) K (Fin 4 → K) :=
  basisOfTopLeSpanOfCardEqFinrank (fun i j => e i (p j)) (by
    have he : Set.range (fun i j => e i (p j)) =
        Set.range (fun σ : L →ₐ[k] K => fun j => σ (p j)) := by
      exact e.surjective.range_comp (fun σ : L →ₐ[k] K => fun j => σ (p j))
    rw [he, hspan]) (by simp)

theorem conjugateBasis_apply (e : Fin 4 ≃ (L →ₐ[k] K)) (p : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (i j : Fin 4) : conjugateBasis e p hspan i j = e i (p j) := by
  simp [conjugateBasis]

theorem conjugateBasis_repr_covariance (e : Fin 4 ≃ (L →ₐ[k] K)) (p : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (g : K ≃ₐ[k] K) (x : Fin 4 → K) (j : Fin 4) :
    (conjugateBasis e p hspan).repr (fun m => g (x m)) (indexedEmbeddingAction e g j) =
      g ((conjugateBasis e p hspan).repr x j) := by
  classical
  let b := conjugateBasis e p hspan
  let π := indexedEmbeddingAction e g
  have hexp : (fun m => g (x m)) = ∑ i, g (b.repr x i) • b (π i) := by
    funext m
    have h := congrArg (fun y : Fin 4 → K => g (y m)) (b.sum_repr x)
    simpa [conjugateBasis_apply, indexedEmbeddingAction_apply, Pi.smul_apply,
      Finset.sum_apply, map_sum, map_mul, smul_eq_mul, b, π] using h.symm
  rw [hexp, map_sum, Finsupp.finset_sum_apply]
  simp [b, π, Finsupp.single_apply]

noncomputable def conjugateTangentRow (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤) :
    Fin 4 → Fin 4 → K :=
  fun i j => (conjugateBasis e p hspan).repr (fun m => e i (v m)) j

noncomputable def conjugateTangentMatrix (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤) :
    Fin 4 → Fin 4 → K :=
  fun i j => if i = j then 0 else conjugateTangentRow e p v hspan i j

theorem conjugateTangentMatrix_diagonal (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (i : Fin 4) : conjugateTangentMatrix e p v hspan i i = 0 := by
  simp [conjugateTangentMatrix]

theorem conjugateTangentMatrix_covariance (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (g : K ≃ₐ[k] K) (i j : Fin 4) :
    g (conjugateTangentMatrix e p v hspan i j) =
      conjugateTangentMatrix e p v hspan
        (indexedEmbeddingAction e g i) (indexedEmbeddingAction e g j) := by
  by_cases hij : i = j
  · subst j
    simp [conjugateTangentMatrix]
  · simp only [conjugateTangentMatrix, Equiv.apply_eq_iff_eq, hij, ↓reduceIte]
    exact (conjugateBasis_repr_covariance e p hspan g (fun m => e i (v m)) j).symm.trans
      (by simp only [conjugateTangentRow, indexedEmbeddingAction_apply])

theorem conjugateTangentMatrix_row_nonzero (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hp : p 0 = 1) (hv0 : v 0 = 0) (hv : v ≠ 0) (i : Fin 4) :
    ∃ j, conjugateTangentMatrix e p v hspan i j ≠ 0 := by
  classical
  by_contra! h
  let b := conjugateBasis e p hspan
  let x : Fin 4 → K := fun m => e i (v m)
  have hz (j : Fin 4) (hj : j ≠ i) : b.repr x j = 0 := by
    simpa [conjugateTangentMatrix, conjugateTangentRow, Ne.symm hj, b, x] using h j
  have he : x = b.repr x i • b i := by
    calc
      x = ∑ j, b.repr x j • b j := (b.sum_repr x).symm
      _ = _ := Finset.sum_eq_single i (fun j _ hj => by rw [hz j hj, zero_smul])
        (fun hi => (hi (Finset.mem_univ i)).elim)
  have hc : b.repr x i = 0 := by
    have hh := congrFun he 0
    simpa [x, b, conjugateBasis_apply, hp, hv0] using hh.symm
  rw [hc, zero_smul] at he
  apply hv
  funext j
  exact (map_eq_zero (e i)).mp (congrFun he j)

theorem conjugateTangentMatrix_transitive_covariance [Normal k K]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (i j : Fin 4) :
    ∃ (π : Equiv.Perm (Fin 4)) (g : K ≃+* K) (r s : Fin 4 → K),
      π i = j ∧ (∀ m, r m ≠ 0) ∧ (∀ m, s m ≠ 0) ∧
      ∀ m n, g (conjugateTangentMatrix e p v hspan m n) =
        r m * s n * conjugateTangentMatrix e p v hspan (π m) (π n) := by
  obtain ⟨g, hg⟩ := indexedEmbeddingAction_transitive e i j
  exact ⟨indexedEmbeddingAction e g, g.toRingEquiv, fun _ => 1, fun _ => 1, hg,
    fun _ => one_ne_zero, fun _ => one_ne_zero, fun m n => by
      simpa using conjugateTangentMatrix_covariance e p v hspan g m n⟩

end QuarticNet
end PfaffianDescent

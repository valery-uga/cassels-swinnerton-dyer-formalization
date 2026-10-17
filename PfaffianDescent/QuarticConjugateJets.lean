import PfaffianDescent.QuarticConjugateCoordinates
import PfaffianDescent.QuarticTangentInterpolation
import AllCharacteristics.HomogeneousSpecialization
import Mathlib.Algebra.DualNumber

/-!
# Homogeneous equations at the conjugate tangent jets

This transports a homogeneous equation through the coordinate basis formed by
the four conjugates of a separable quartic point.  A first-order equation at
the original dual point consequently vanishes at all four coordinate tangent
jets after base change.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module TrivSqZeroExt

variable {k L K : Type*} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]

noncomputable def dualNumberEmbedding (σ : L →ₐ[k] K) :
    DualNumber L →ₐ[k] DualNumber K where
  toFun x := (σ x.fst, σ x.snd)
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by
    change (σ (x + y).fst, σ (x + y).snd) =
      (σ x.fst, σ x.snd) + (σ y.fst, σ y.snd)
    apply TrivSqZeroExt.ext
    · exact σ.map_add _ _
    · exact σ.map_add _ _
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · change σ (x.fst * y.fst) = σ x.fst * σ y.fst
      exact σ.map_mul _ _
    · change σ (x.fst * y.snd + x.snd * y.fst) =
        σ x.fst * σ y.snd + σ x.snd * σ y.fst
      simp only [map_add, map_mul]
  commutes' c := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

@[simp] theorem dualNumberEmbedding_apply (σ : L →ₐ[k] K) (x : DualNumber L) :
    dualNumberEmbedding σ x = (σ x.fst, σ x.snd) := rfl

theorem dualNumberEmbedding_aeval (σ : L →ₐ[k] K) (p v : Fin 4 → L)
    (F : MvPolynomial (Fin 4) k) :
    dualNumberEmbedding σ (aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F) =
      aeval (R := k) (S₁ := DualNumber K)
        (fun i => TrivSqZeroExt.inl (σ (p i)) + TrivSqZeroExt.inr (σ (v i))) F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
      exact (dualNumberEmbedding σ).commutes a
  | add F G hF hG => rw [map_add, map_add, hF, hG, map_add]
  | mul_X F i hF =>
      rw [map_mul]
      rw [MvPolynomial.aeval_X]
      change dualNumberEmbedding σ
        (aeval (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F *
          (TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i))) = _
      rw [map_mul, hF, map_mul, MvPolynomial.aeval_X]
      congr 1
      rw [dualNumberEmbedding_apply]
      apply TrivSqZeroExt.ext
      · simp
      · simp

theorem aeval_linearSubstitution {A : Type*} [CommRing A] [Algebra K A]
    (M : Matrix (Fin 4) (Fin 4) K) (x : Fin 4 → A)
    (F : MvPolynomial (Fin 4) K) :
    aeval x (linearSubstitution M F) =
      aeval (fun i => ∑ j, algebraMap K A (M i j) * x j) F := by
  have h : (aeval x).comp (linearSubstitution M) =
      aeval (fun i => ∑ j, algebraMap K A (M i j) * x j) := by
    ext i : 1
    rw [AlgHom.comp_apply, linearSubstitution_X, aeval_X]
    change aeval x (linearCoordinate M i) = _
    simp [linearCoordinate, Matrix.mulVec, dotProduct]
  exact AlgHom.congr_fun h F

theorem aeval_smul_of_homogeneous {A : Type*} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin 4) K) (n : ℕ) (hF : F.IsHomogeneous n)
    (c : A) (x : Fin 4 → A) :
    aeval (c • x) F = c ^ n * aeval x F := by
  exact AllCharacteristics.eval₂_homogeneous_smul F hF (algebraMap K A) x c

noncomputable def basisCoordinateMatrix (b : Basis (Fin 4) K (Fin 4 → K)) :
    Matrix (Fin 4) (Fin 4) K := fun m i => b i m

theorem basisCoordinateMatrix_isUnit (b : Basis (Fin 4) K (Fin 4 → K)) :
    IsUnit (basisCoordinateMatrix b).det := by
  let N : Matrix (Fin 4) (Fin 4) K :=
    fun i m => b.repr (Pi.single m (1 : K)) i
  apply Matrix.isUnit_det_of_right_inverse (B := N)
  ext m n
  have h := congrFun (b.sum_repr (Pi.single n (1 : K))) m
  change ∑ i, b i m * b.repr (Pi.single n (1 : K)) i = if m = n then 1 else 0
  calc
    ∑ i, b i m * b.repr (Pi.single n (1 : K)) i =
        ∑ i, b.repr (Pi.single n (1 : K)) i * b i m := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (Pi.single n (1 : K) : Fin 4 → K) m := by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
    _ = if m = n then 1 else 0 := by simp [Pi.single_apply, eq_comm]

theorem conjugateTangentMatrix_expansion (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (i m : Fin 4) :
    ∑ j, (conjugateBasis e p hspan j m) * conjugateTangentMatrix e p v hspan i j =
      e i (v m) - conjugateTangentRow e p v hspan i i * e i (p m) := by
  classical
  have hu (j : Fin 4) : conjugateTangentMatrix e p v hspan i j =
      conjugateTangentRow e p v hspan i j -
        if i = j then conjugateTangentRow e p v hspan i i else 0 := by
    by_cases hij : i = j <;> simp [conjugateTangentMatrix, hij]
  simp only [hu, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  have he := congrFun ((conjugateBasis e p hspan).sum_repr (fun j => e i (v j))) m
  have he' : ∑ j, (conjugateBasis e p hspan j m) *
      conjugateTangentRow e p v hspan i j = e i (v m) := by
    simpa [conjugateTangentRow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using he
  rw [he', conjugateBasis_apply]
  simp [mul_comm]

theorem conjugate_dual_coordinates (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (i m : Fin 4) :
    ∑ j, algebraMap K (DualNumber K) (basisCoordinateMatrix (conjugateBasis e p hspan) m j) *
      tangentDualPoint (conjugateTangentMatrix e p v hspan) i j =
      (1 + TrivSqZeroExt.inr (-conjugateTangentRow e p v hspan i i) : DualNumber K) *
        (TrivSqZeroExt.inl (e i (p m)) + TrivSqZeroExt.inr (e i (v m))) := by
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mk,
      tangentDualPoint, basisCoordinateMatrix, TrivSqZeroExt.algebraMap_eq_inl,
      mul_ite, Finset.sum_ite_eq, conjugateBasis_apply]
  · simpa [TrivSqZeroExt.snd_sum, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk,
      tangentDualPoint, basisCoordinateMatrix, TrivSqZeroExt.algebraMap_eq_inl,
      DualNumber.snd_mul, sub_eq_add_neg] using
        conjugateTangentMatrix_expansion e p v hspan i m

theorem homogeneous_jet_vanishes_on_conjugates
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (F : MvPolynomial (Fin 4) k) (n : ℕ) (hF : F.IsHomogeneous n)
    (hvan : aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F = 0) (i : Fin 4) :
    aeval (tangentDualPoint (conjugateTangentMatrix e p v hspan) i)
      (linearSubstitution (basisCoordinateMatrix (conjugateBasis e p hspan))
        (map (algebraMap k K) F)) = 0 := by
  let c : DualNumber K := 1 + TrivSqZeroExt.inr (-conjugateTangentRow e p v hspan i i)
  let y : Fin 4 → DualNumber K := fun j =>
    TrivSqZeroExt.inl (e i (p j)) + TrivSqZeroExt.inr (e i (v j))
  let M := basisCoordinateMatrix (conjugateBasis e p hspan)
  let U := conjugateTangentMatrix e p v hspan
  have hx : (fun m => ∑ j, algebraMap K (DualNumber K) (M m j) * tangentDualPoint U i j) =
      c • y := by
    funext m
    exact conjugate_dual_coordinates e p v hspan i m
  change aeval (tangentDualPoint U i) (linearSubstitution M (map (algebraMap k K) F)) = 0
  rw [aeval_linearSubstitution, hx]
  rw [aeval_smul_of_homogeneous _ n (hF.map (algebraMap k K))]
  have hy : aeval y (map (algebraMap k K) F) = (dualNumberEmbedding (e i))
      (aeval (R := k) (S₁ := DualNumber L)
        (fun j => TrivSqZeroExt.inl (p j) + TrivSqZeroExt.inr (v j)) F) := by
    rw [dualNumberEmbedding_aeval]
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq k K (DualNumber K)]
    apply congrArg (fun z : Fin 4 → DualNumber K => aeval (R := k) z F)
    funext j
    apply TrivSqZeroExt.ext <;> simp [y]
  rw [hy, hvan, map_zero, mul_zero]

end QuarticNet
end PfaffianDescent

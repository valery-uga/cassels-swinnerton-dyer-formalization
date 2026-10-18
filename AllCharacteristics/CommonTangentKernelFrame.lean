import AllCharacteristics.SecantPolarQuadricLift
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A surjective pair of linear equations on four
coordinates has a two-column kernel frame that spans the kernel after every
field extension. All scalar-extension assertions follow from matrix
left/right inverse identities. -/

noncomputable section
namespace PfaffianDescent
open scoped BigOperators
universe u

section Pair
variable {K : Type u} [Field K]

def coordinatePairMatrix (a b : Fin 4 → K) : Matrix (Fin 2) (Fin 4) K := ![a, b]

theorem coordinatePairMatrix_mulVec (a b x : Fin 4 → K) :
    (coordinatePairMatrix a b).mulVec x =
      ![Cubic.coordinateLinearMap a x, Cubic.coordinateLinearMap b x] := by
  funext i
  fin_cases i <;> rfl

/-- Mutual tangent separation supplies surjectivity of the two tangent
equations, using the two centers themselves as transverse test vectors. -/
theorem coordinatePairMatrix_mulVec_surjective
    (a b p q : Fin 4 → K)
    (hap : Cubic.coordinateLinearMap a p = 0)
    (hbq : Cubic.coordinateLinearMap b q = 0)
    (haq : Cubic.coordinateLinearMap a q ≠ 0)
    (hbp : Cubic.coordinateLinearMap b p ≠ 0) :
    Function.Surjective (coordinatePairMatrix a b).mulVec := by
  let U := Cubic.coordinateLinearMap a
  let V := Cubic.coordinateLinearMap b
  intro y
  let w : Fin 4 → K := (y 0 / U q) • q + (y 1 / V p) • p
  refine ⟨w, ?_⟩
  rw [coordinatePairMatrix_mulVec]
  funext i
  fin_cases i
  · change U w = y 0
    dsimp only [w]
    rw [U.map_add, U.map_smul, U.map_smul, hap]
    simp only [smul_eq_mul, mul_zero, add_zero]
    exact div_mul_cancel₀ _ haq
  · change V w = y 1
    dsimp only [w]
    rw [V.map_add, V.map_smul, V.map_smul, hbq]
    simp only [smul_eq_mul, mul_zero, zero_add]
    exact div_mul_cancel₀ _ hbp

end Pair

theorem finrank_kernel_two_of_surjective_pair
    {K : Type u} [Field K] (R : Matrix (Fin 2) (Fin 4) K)
    (hR : Function.Surjective R.mulVec) :
    Module.finrank K (LinearMap.ker R.mulVecLin) = 2 := by
  have hrange : LinearMap.range R.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr hR
  have h := R.mulVecLin.finrank_range_add_finrank_ker
  rw [hrange] at h
  simp at h
  omega

/-- A kernel basis together with an ambient retraction and a right inverse
of the pair of equations. These are actual finite matrices, so the frame
and its dimension survive every coefficient field extension. -/
theorem exists_split_kernel_frame_of_surjective_pair
    {K : Type u} [Field K] (R : Matrix (Fin 2) (Fin 4) K)
    (hR : Function.Surjective R.mulVec) :
    ∃ (A : Matrix (Fin 4) (Fin 2) K) (B : Matrix (Fin 2) (Fin 4) K)
      (S : Matrix (Fin 4) (Fin 2) K),
      B * A = 1 ∧ R * A = 0 ∧ R * S = 1 := by
  classical
  let W := LinearMap.ker R.mulVecLin
  let b : Module.Basis (Fin 2) K W :=
    Module.finBasisOfFinrankEq K W (finrank_kernel_two_of_surjective_pair R hR)
  let g : (Fin 2 → K) →ₗ[K] (Fin 4 → K) :=
    W.subtype.comp b.equivFun.symm.toLinearMap
  have hginj : Function.Injective g :=
    Subtype.val_injective.comp b.equivFun.symm.injective
  obtain ⟨l, hl⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hginj)
  obtain ⟨s, hs⟩ := R.mulVecLin.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hR)
  let A := LinearMap.toMatrix' g
  let B := LinearMap.toMatrix' l
  let S := LinearMap.toMatrix' s
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, hl, LinearMap.toMatrix'_id]
  have hRS : R * S = 1 := by
    have he := congrArg LinearMap.toMatrix' hs
    have hRmat : LinearMap.toMatrix' R.mulVecLin = R :=
      LinearMap.toMatrix'_toLin' R
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
      hRmat] using he
  have hRA : R * A = 0 := by
    have hzero (x : Fin 2 → K) : (R * A).mulVec x = 0 := by
      rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      exact (b.equivFun.symm x).property
    ext i j
    have hi := congrArg (fun v : Fin 2 → K ↦ v i) (hzero (Pi.single j 1))
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply,
      Pi.zero_apply, Matrix.zero_apply] using hi
  exact ⟨A, B, S, hBA, hRA, hRS⟩

/-- The split frame spans the common kernel after arbitrary field
extension; this is the exact spanning certificate used for common-line
root descent in the secant construction. -/
theorem mapped_kernel_frame_spans
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (R : Matrix (Fin 2) (Fin 4) K)
    (A : Matrix (Fin 4) (Fin 2) K) (B : Matrix (Fin 2) (Fin 4) K)
    (S : Matrix (Fin 4) (Fin 2) K)
    (hBA : B * A = 1) (hRA : R * A = 0) (hRS : R * S = 1)
    (z : Fin 4 → L) (hz : (R.map f).mulVec z = 0) :
    ∃ s t : L, z =
      s • (fun i ↦ f (A i 0)) + t • (fun i ↦ f (A i 1)) := by
  have hBAf : B.map f * A.map f = 1 := by
    rw [← Matrix.map_mul, hBA]
    simp
  have hRAf : R.map f * A.map f = 0 := by
    rw [← Matrix.map_mul, hRA]
    simp
  have hRSf : R.map f * S.map f = 1 := by
    rw [← Matrix.map_mul, hRS]
    simp
  have hAinj : Function.Injective (A.map f).mulVec := by
    intro x y hxy
    have he := congrArg ((B.map f).mulVec) hxy
    simpa only [Matrix.mulVec_mulVec, hBAf, Matrix.one_mulVec] using he
  have hRsurj : Function.Surjective (R.map f).mulVec := by
    intro y
    refine ⟨(S.map f).mulVec y, ?_⟩
    rw [Matrix.mulVec_mulVec, hRSf, Matrix.one_mulVec]
  have hle : LinearMap.range (A.map f).mulVecLin ≤
      LinearMap.ker (R.map f).mulVecLin := by
    rintro _ ⟨x, rfl⟩
    change (R.map f).mulVec ((A.map f).mulVec x) = 0
    rw [Matrix.mulVec_mulVec, hRAf, Matrix.zero_mulVec]
  have hdimA : Module.finrank L (LinearMap.range (A.map f).mulVecLin) = 2 := by
    simpa using LinearMap.finrank_range_of_inj (f := (A.map f).mulVecLin) hAinj
  have heq : LinearMap.range (A.map f).mulVecLin =
      LinearMap.ker (R.map f).mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle
      (hdimA.trans (finrank_kernel_two_of_surjective_pair (R.map f) hRsurj).symm)
  have hzmem : z ∈ LinearMap.range (A.map f).mulVecLin := by
    rw [heq]
    exact hz
  obtain ⟨y, hy⟩ := hzmem
  refine ⟨y 0, y 1, ?_⟩
  rw [← hy]
  change (A.map f).mulVec y = _
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PfaffianDescent

import PfaffianDescent.VoisinQuadraticFrameDetectionDescent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Extension-stability of the finite matrix that evaluates the fixed
quadratic frame on eight chosen points. -/

namespace PfaffianDescent

open MvPolynomial

universe u

/-- The eight-by-eight matrix obtained by evaluating the fixed frame at
eight coordinate vectors. -/
noncomputable def quadraticEightEvaluationMatrix
    (K : Type u) [Field K] (x : Fin 8 → Fin 4 → K) :
    Matrix (Fin 8) (Fin 8) K :=
  fun i j => eval (x i) (quadraticEightFrame K j).1

/-- Evaluating a frame combination is multiplication by its evaluation
matrix. -/
theorem quadraticEightEvaluationMatrix_mulVec
    (K : Type u) [Field K] (x : Fin 8 → Fin 4 → K)
    (c : Fin 8 → K) (i : Fin 8) :
    (quadraticEightEvaluationMatrix K x).mulVec c i =
      eval (x i) (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 := by
  simp [quadraticEightEvaluationMatrix, Matrix.mulVec, dotProduct,
    homogeneousFrameMap, Fintype.linearCombination_apply,
    MvPolynomial.smul_eq_C_mul, mul_comm]

/-- The evaluation matrix itself commutes with coefficient extension. -/
theorem quadraticEightEvaluationMatrix_map
    {K L : Type u} [Field K] [Field L]
    (b : K →+* L) (x : Fin 8 → Fin 4 → K) :
    quadraticEightEvaluationMatrix L
      (fun i j => b (x i j)) =
        (quadraticEightEvaluationMatrix K x).map b := by
  ext i j
  simp only [quadraticEightEvaluationMatrix, Matrix.map_apply]
  rw [← quadraticEightFrame_map b j, MvPolynomial.eval_map]
  simpa only [Function.comp_def] using
    (MvPolynomial.eval₂_comp b (x i) (quadraticEightFrame K j).1).symm

/-- A square evaluation matrix that is injective over one field remains
injective after an arbitrary further extension of that field. -/
theorem eightEvaluationMatrix_injective_after_extension
    {K L : Type u} [Field K] [Field L]
    (b : K →+* L) (M : Matrix (Fin 8) (Fin 8) K)
    (hM : Function.Injective M.mulVec) :
    Function.Injective (M.map b).mulVec := by
  have hunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hM
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunit
  have hdetL : IsUnit (M.map b).det := by
    have h := hdet.map b
    simpa only [b.map_det, RingHom.mapMatrix_apply, Matrix.map_apply] using h
  exact Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det (M.map b)).mpr hdetL)

/-- If the eight selected coordinate vectors detect the fixed frame over
their field, they continue to detect it over every further field extension.
Thus a projective-incidence witness over a larger residue field cannot
introduce a new linear relation among the eight evaluations. -/
theorem quadraticEightFrame_detection_persists
    {K L : Type u} [Field K] [Field L]
    (b : K →+* L) (x : Fin 8 → Fin 4 → K)
    (hdetect : ∀ c : Fin 8 → K,
      (∀ i, eval (x i)
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0) :
    ∀ c : Fin 8 → L,
      (∀ i, eval (fun j => b (x i j))
        (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
      c = 0 := by
  let M := quadraticEightEvaluationMatrix K x
  have hM : Function.Injective M.mulVec := by
    intro c d hcd
    apply sub_eq_zero.mp
    apply hdetect (c - d)
    intro i
    rw [← quadraticEightEvaluationMatrix_mulVec]
    have hz : M.mulVec (c - d) = 0 := by
      rw [Matrix.mulVec_sub, hcd, sub_self]
    exact congrFun hz i
  have hML := eightEvaluationMatrix_injective_after_extension b M hM
  intro c hc
  apply hML.eq_iff.mp
  rw [← quadraticEightEvaluationMatrix_map b x]
  funext i
  rw [quadraticEightEvaluationMatrix_mulVec]
  exact (hc i).trans (by simp)

/-- Multiplying each of the eight coordinate vectors by its own nonzero
scalar preserves detection of the homogeneous quadratic frame. -/
theorem quadraticEightFrame_detection_rowScaling
    {K : Type u} [Field K]
    (x : Fin 8 → Fin 4 → K) (s : Fin 8 → K)
    (hs : ∀ i, s i ≠ 0)
    (hdetect : ∀ c : Fin 8 → K,
      (∀ i, eval (x i)
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0) :
    ∀ c : Fin 8 → K,
      (∀ i, eval (s i • x i)
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0 := by
  intro c hc
  apply hdetect c
  intro i
  have hhom : (homogeneousFrameMap 2
      (quadraticEightFrame K) c).1.IsHomogeneous 2 :=
    (homogeneousFrameMap 2 (quadraticEightFrame K) c).2
  have hi := hc i
  change MvPolynomial.aeval (s i • x i)
    (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0 at hi
  change MvPolynomial.aeval (x i)
    (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0
  rw [aeval_smul_of_isHomogeneous _ hhom] at hi
  exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero 2 (hs i))

end PfaffianDescent

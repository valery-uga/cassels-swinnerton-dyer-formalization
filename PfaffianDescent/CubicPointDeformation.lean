import PfaffianDescent.CubicEvaluation
import PfaffianDescent.CubicMap
import PfaffianDescent.PolynomialBasis
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace PfaffianDescent
open Polynomial Module
open scoped BigOperators
attribute [local instance] Polynomial.algebra
noncomputable section

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- The linearly moving extension-field point. -/
def pointDeformation (p q : Vec L n) : Vec L[X] n :=
  (1 - (X : L[X])) • (fun i => C (p i)) + (X : L[X]) • (fun i => C (q i))

theorem pointDeformation_zero (p q : Vec L n) :
    (fun i => (pointDeformation p q i).eval 0) = p := by
  funext i
  simp [pointDeformation, Pi.smul_apply]

theorem pointDeformation_one (p q : Vec L n) :
    (fun i => (pointDeformation p q i).eval 1) = q := by
  funext i
  simp [pointDeformation, Pi.smul_apply]

/-- Evaluate a ground-field cubic on polynomial coordinates. -/
def polynomialCubicEvaluation (P : Vec L[X] n) (c : Cubic K n) : L[X] :=
  (c.map (C.comp (algebraMap K L))).eval P

theorem polynomialCubicEvaluation_at (P : Vec L[X] n) (c : Cubic K n) (t : L) :
    (polynomialCubicEvaluation P c).eval t =
      (c.map (algebraMap K L)).eval (fun i => (P i).eval t) := by
  have h := Cubic.eval_map (evalRingHom t) (c.map (C.comp (algebraMap K L))) P
  have hc : (c.map (C.comp (algebraMap K L))).map (evalRingHom t) = c.map (algebraMap K L) := by
    funext i
    exact eval_C
  rw [hc] at h
  exact h.symm

theorem constantCubic_map (f : K →+* L) (c : Cubic K n) :
    (c.map C).map (mapRingHom f) = c.map (C.comp f) := by
  funext i
  exact Polynomial.map_C f

theorem constantCubic_eval (c : Cubic K n) (t : K) :
    (c.map C).map (evalRingHom t) = c := by
  funext i
  exact eval_C

/-- Choose polynomial cubic coefficients that vanish at a moving point, while
recovering the original cubic at parameter zero. Surjectivity is used only to
choose a finite evaluation frame in the residue field. -/
theorem deform_cubic_through_point {m : ℕ} (b : Basis (Fin m) K L)
    (p q : Vec L n) (c : Cubic K n)
    (hF : (c.map (algebraMap K L)).eval p = 0)
    (d : Fin m → Cubic K n) (hd : ∀ j, cubicEvaluation p (d j) = b j) :
    ∃ F : Cubic K[X] n,
      (F.map (mapRingHom (algebraMap K L))).eval (pointDeformation p q) = 0 ∧
      F.map (evalRingHom 0) = c := by
  let P := pointDeformation p q
  let E := polynomialCubicEvaluation (K := K) P
  let N : Mat K[X] m := fun i j => basisPolynomialCoordinates b (E (d j)) i
  let v : Vec K[X] m := basisPolynomialCoordinates b (E c)
  let w := N.adjugate.mulVec v
  let F : Cubic K[X] n := N.det • c.map C - ∑ j, w j • (d j).map C
  have hN : N.mulVec w = N.det • v := by
    change N.mulVec (N.adjugate.mulVec v) = N.det • v
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcol : ∀ j, basisPolynomialLift b (fun i => N i j) = E (d j) :=
    fun j => basisPolynomialLift_reconstruct b (E (d j))
  have hsum : (∑ j, w j • E (d j)) = N.det • E c := by
    have h := congrArg (basisPolynomialLift b) hN
    rw [linearMap_mulVec, map_smul, basisPolynomialLift_reconstruct] at h
    simpa only [hcol] using h
  have hzero : (F.map (mapRingHom (algebraMap K L))).eval P = 0 := by
    simp only [F, Cubic.map_sub, Cubic.map_coefficient_smul, Cubic.map_sum,
      constantCubic_map, Cubic.eval_sub, Cubic.eval_coefficient_smul, Cubic.eval_sum]
    change (mapRingHom (algebraMap K L)) N.det * E c -
      (∑ j, (mapRingHom (algebraMap K L)) (w j) * E (d j)) = 0
    change N.det • E c - (∑ j, w j • E (d j)) = 0
    rw [hsum, sub_self]
  have hE0 : ∀ f : Cubic K n, (E f).eval 0 = cubicEvaluation p f := by
    intro f
    rw [polynomialCubicEvaluation_at, pointDeformation_zero, cubicEvaluation_eq]
  have hN0 : N.map (evalRingHom 0) = 1 := by
    ext i j
    change (basisPolynomialCoordinates b (E (d j)) i).eval 0 = (1 : Mat K m) i j
    rw [basisPolynomialCoordinates_eval_zero, hE0, hd]
    simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
  have hv0 : (evalRingHom 0) ∘ v = 0 := by
    funext i
    change (basisPolynomialCoordinates b (E c) i).eval 0 = 0
    rw [basisPolynomialCoordinates_eval_zero, hE0, cubicEvaluation_eq, hF]
    simp only [map_zero, Finsupp.zero_apply]
  have hw0 : ∀ i, (w i).eval 0 = 0 := by
    intro i
    have h := (evalRingHom (0 : K)).map_mulVec N.adjugate v i
    rw [hv0, Matrix.mulVec_zero] at h
    exact h
  have hdet0 : N.det.eval 0 = 1 := by
    have h := (evalRingHom (0 : K)).map_det N
    change (evalRingHom (0 : K)) N.det = (N.map (evalRingHom 0)).det at h
    rw [hN0, Matrix.det_one] at h
    exact h
  refine ⟨F, hzero, ?_⟩
  simp only [F, Cubic.map_sub, Cubic.map_coefficient_smul, Cubic.map_sum,
    constantCubic_eval]
  simp only [coe_evalRingHom, hdet0, hw0, one_smul, zero_smul, Finset.sum_const_zero, sub_zero]

end
end
end PfaffianDescent

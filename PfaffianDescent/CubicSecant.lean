import PfaffianDescent.Cubic

namespace PfaffianDescent
namespace Cubic

section
variable {R : Type*} [CommRing R] {n : ℕ}

/-- The residual point of the line through two cubic points, written in
homogeneous coordinates. -/
def secantResidualPoint (c : Cubic R n) (p q : Vec R n) : Vec R n :=
  c.mixed q p • p - c.mixed p q • q

/-- If `p` and `q` lie on a cubic, their residual secant point lies on it. -/
theorem eval_secantResidualPoint
    (c : Cubic R n) (p q : Vec R n)
    (hp : c.eval p = 0) (hq : c.eval q = 0) :
    c.eval (secantResidualPoint c p q) = 0 := by
  rw [secantResidualPoint, show c.mixed q p • p - c.mixed p q • q =
      c.mixed q p • p + (-(c.mixed p q)) • q by
        simp only [sub_eq_add_neg, neg_smul],
    c.eval_line, hp, hq]
  ring

/-- The residual point of a line tangent to the cubic at its first point. -/
def tangentResidualPoint (c : Cubic R n) (p d : Vec R n) : Vec R n :=
  c.eval d • p - c.mixed d p • d

/-- A tangent line meets the cubic again at `tangentResidualPoint`. -/
theorem eval_tangentResidualPoint
    (c : Cubic R n) (p d : Vec R n)
    (hp : c.eval p = 0) (htan : c.mixed p d = 0) :
    c.eval (tangentResidualPoint c p d) = 0 := by
  rw [tangentResidualPoint, show c.eval d • p - c.mixed d p • d =
      c.eval d • p + (-(c.mixed d p)) • d by
        simp only [sub_eq_add_neg, neg_smul],
    c.eval_line, hp, htan]
  ring

/-- The tangent residual construction commutes with extending coefficients. -/
theorem map_tangentResidualPoint
    {S : Type*} [CommRing S] (f : R →+* S)
    (c : Cubic R n) (p d : Vec R n) :
    tangentResidualPoint (c.map f) (fun i ↦ f (p i)) (fun i ↦ f (d i)) =
      fun i ↦ f (tangentResidualPoint c p d i) := by
  funext i
  simp only [tangentResidualPoint, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Cubic.eval_map, Cubic.mixed_map, map_sub, map_mul]

/-- The residual-point construction commutes with extending coefficients. -/
theorem map_secantResidualPoint
    {S : Type*} [CommRing S] (f : R →+* S)
    (c : Cubic R n) (p q : Vec R n) :
    secantResidualPoint (c.map f) (fun i ↦ f (p i)) (fun i ↦ f (q i)) =
      fun i ↦ f (secantResidualPoint c p q i) := by
  funext i
  simp only [secantResidualPoint, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Cubic.mixed_map, map_sub, map_mul]

end

section
variable {K : Type*} [Field K] {n : ℕ}

/-- The residual tangent point is nonzero when the direction is independent
from the tangency point and is not itself on the cubic. -/
theorem tangentResidualPoint_ne_zero
    (c : Cubic K n) (p d : Vec K n)
    (hind : LinearIndependent K ![p, d])
    (hdir : c.eval d ≠ 0) :
    tangentResidualPoint c p d ≠ 0 := by
  intro hz
  change c.eval d • p - c.mixed d p • d = 0 at hz
  have hsum : ∑ i : Fin 2, ![c.eval d, -(c.mixed d p)] i • ![p, d] i = 0 := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Fin.isValue, sub_eq_add_neg, neg_smul] using hz
  have hcoeff := Fintype.linearIndependent_iff.mp hind _ hsum
  exact hdir (hcoeff 0)

/-- The residual secant point is nonzero when the two starting points are
independent and the line is not tangent at its first point. -/
theorem secantResidualPoint_ne_zero
    (c : Cubic K n) (p q : Vec K n)
    (hind : LinearIndependent K ![p, q])
    (hsec : c.mixed p q ≠ 0) :
    secantResidualPoint c p q ≠ 0 := by
  intro hz
  change c.mixed q p • p - c.mixed p q • q = 0 at hz
  have hsum : ∑ i : Fin 2, ![c.mixed q p, -(c.mixed p q)] i • ![p, q] i = 0 := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Fin.isValue, sub_eq_add_neg, neg_smul] using hz
  have hcoeff := Fintype.linearIndependent_iff.mp hind _ hsum
  exact hsec (neg_eq_zero.mp (hcoeff 1))

end
end Cubic
end PfaffianDescent

namespace PfaffianDescent
namespace Cubic

section
variable {R : Type*} [CommRing R] {n : ℕ}

/-- The third point obtained by taking secants between two tangent residual
points through the same cubic point. -/
def tangentSecantResidual (c : Cubic R n) (p d e : Vec R n) : Vec R n :=
  secantResidualPoint c (tangentResidualPoint c p d) (tangentResidualPoint c p e)

/-- The tangent--secant construction remains on the cubic. -/
theorem eval_tangentSecantResidual
    (c : Cubic R n) (p d e : Vec R n)
    (hp : c.eval p = 0) (hd : c.mixed p d = 0) (he : c.mixed p e = 0) :
    c.eval (tangentSecantResidual c p d e) = 0 := by
  apply eval_secantResidualPoint
  · exact eval_tangentResidualPoint c p d hp hd
  · exact eval_tangentResidualPoint c p e hp he

/-- The tangent--secant construction commutes with coefficient extension. -/
theorem map_tangentSecantResidual
    {S : Type*} [CommRing S] (f : R →+* S)
    (c : Cubic R n) (p d e : Vec R n) :
    tangentSecantResidual (c.map f) (fun i ↦ f (p i)) (fun i ↦ f (d i))
      (fun i ↦ f (e i)) =
    fun i ↦ f (tangentSecantResidual c p d e i) := by
  unfold tangentSecantResidual
  rw [map_tangentResidualPoint f c p d, map_tangentResidualPoint f c p e]
  exact map_secantResidualPoint f c (tangentResidualPoint c p d)
    (tangentResidualPoint c p e)

end
end Cubic
end PfaffianDescent

namespace PfaffianDescent
namespace Cubic

section
variable {R : Type*} [CommRing R] {n : ℕ}

/-- The mixed coefficient is linear in its second vector argument. -/
theorem mixed_add_right (c : Cubic R n) (p d e : Vec R n) :
    c.mixed p (d + e) = c.mixed p d + c.mixed p e := by
  simp only [mixed, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The mixed coefficient is homogeneous of degree one in its second vector
argument. -/
theorem mixed_smul_right (c : Cubic R n) (p d : Vec R n) (r : R) :
    c.mixed p (r • d) = r * c.mixed p d := by
  simp only [mixed, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end

section
variable {K : Type*} [Field K] {n : ℕ}

/-- The linear form cutting out the tangent hyperplane at a point of a cubic. -/
def tangentLinear (c : Cubic K n) (p : Vec K n) : Vec K n →ₗ[K] K where
  toFun d := c.mixed p d
  map_add' d e := mixed_add_right c p d e
  map_smul' r d := by
    rw [mixed_smul_right]
    rfl

@[simp] theorem tangentLinear_apply (c : Cubic K n) (p d : Vec K n) :
    tangentLinear c p d = c.mixed p d := rfl

/-- Membership in the tangent hyperplane is exactly vanishing of the mixed
coefficient. -/
theorem tangentLinear_mem_ker_iff (c : Cubic K n) (p d : Vec K n) :
    d ∈ LinearMap.ker (tangentLinear c p) ↔ c.mixed p d = 0 := by
  rfl

/-- Tangent residual points are cubic points for directions in the tangent
hyperplane. -/
theorem eval_tangentResidualPoint_of_mem_tangentLinear_ker
    (c : Cubic K n) (p d : Vec K n) (hp : c.eval p = 0)
    (hd : d ∈ LinearMap.ker (tangentLinear c p)) :
    c.eval (tangentResidualPoint c p d) = 0 :=
  eval_tangentResidualPoint c p d hp hd

end
end Cubic
end PfaffianDescent

namespace PfaffianDescent
namespace Cubic

section
variable {K : Type*} [Field K] {n : ℕ}

/-- A cubic point and a vector with nonzero cubic value are linearly
independent. -/
theorem linearIndependent_pair_of_eval_zero_eval_ne_zero
    (c : Cubic K n) (p d : Vec K n)
    (hp : p ≠ 0) (hpeval : c.eval p = 0) (hdeval : c.eval d ≠ 0) :
    LinearIndependent K ![p, d] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hd
    change d = 0 at hd
    apply hdeval
    rw [hd, Cubic.eval_zero]
  · intro a h
    change a • d = p at h
    have he : a ^ 3 * c.eval d = 0 := by
      calc
        a ^ 3 * c.eval d = c.eval (a • d) := (Cubic.eval_smul c d a).symm
        _ = c.eval p := by rw [h]
        _ = 0 := hpeval
    have ha3 : a ^ 3 = 0 := (mul_eq_zero.mp he).resolve_right hdeval
    have ha : a = 0 := by
      by_contra ha
      exact (pow_ne_zero 3 ha) ha3
    apply hp
    rw [← h, ha, zero_smul]

/-- The residual tangent point is nonzero as soon as the original cubic point
and tangent direction have respectively zero and nonzero cubic values. -/
theorem tangentResidualPoint_ne_zero_of_eval_ne_zero
    (c : Cubic K n) (p d : Vec K n)
    (hp : p ≠ 0) (hpeval : c.eval p = 0) (hdeval : c.eval d ≠ 0) :
    tangentResidualPoint c p d ≠ 0 :=
  tangentResidualPoint_ne_zero c p d
    (linearIndependent_pair_of_eval_zero_eval_ne_zero c p d hp hpeval hdeval)
    hdeval

end
end Cubic
end PfaffianDescent

namespace PfaffianDescent
namespace Cubic

section
variable {R : Type*} [CommRing R] {n : ℕ}

/-- Evaluating the tangent coefficient at the point itself gives three times
its cubic value. -/
theorem mixed_self_eq_three_eval (c : Cubic R n) (p : Vec R n) :
    c.mixed p p = (3 : R) * c.eval p := by
  simp only [mixed, eval]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end

section
variable {K : Type*} [Field K] {n : ℕ}

/-- A cubic point belongs to the kernel of its tangent linear form. -/
theorem self_mem_tangentLinear_ker (c : Cubic K n) (p : Vec K n)
    (hp : c.eval p = 0) :
    p ∈ LinearMap.ker (tangentLinear c p) := by
  rw [tangentLinear_mem_ker_iff, mixed_self_eq_three_eval, hp, mul_zero]

end
end Cubic
end PfaffianDescent

namespace PfaffianDescent
namespace Cubic

section
variable {K : Type*} [Field K] {n : ℕ}

/-- The tangent--secant residual point is nonzero when its two residual tangent
points are independent and have a genuine secant coefficient. -/
theorem tangentSecantResidual_ne_zero
    (c : Cubic K n) (p d e : Vec K n)
    (hind : LinearIndependent K
      ![tangentResidualPoint c p d, tangentResidualPoint c p e])
    (hsec : c.mixed (tangentResidualPoint c p d)
      (tangentResidualPoint c p e) ≠ 0) :
    tangentSecantResidual c p d e ≠ 0 := by
  unfold tangentSecantResidual
  exact secantResidualPoint_ne_zero c
    (tangentResidualPoint c p d) (tangentResidualPoint c p e) hind hsec

end
end Cubic
end PfaffianDescent
namespace PfaffianDescent
namespace Cubic

section
variable {R : Type*} [CommRing R] {n : ℕ}

lemma mixed_tangentResidualPoint
    (c : Cubic R n) (p d : Vec R n) :
    c.mixed p (tangentResidualPoint c p d) =
      c.eval d * c.mixed p p - c.mixed d p * c.mixed p d := by
  rw [tangentResidualPoint, show c.eval d • p - c.mixed d p • d =
      c.eval d • p + (-(c.mixed d p)) • d by
        simp only [sub_eq_add_neg, neg_smul],
    mixed_add_right, mixed_smul_right, mixed_smul_right]
  ring

/-- The residual point on a tangent line remains in the tangent hyperplane. -/
theorem mixed_tangentResidualPoint_eq_zero
    (c : Cubic R n) (p d : Vec R n)
    (hp : c.eval p = 0) (hd : c.mixed p d = 0) :
    c.mixed p (tangentResidualPoint c p d) = 0 := by
  rw [mixed_tangentResidualPoint, mixed_self_eq_three_eval, hp, hd]
  ring

lemma mixed_secantResidualPoint
    (c : Cubic R n) (p q r : Vec R n) :
    c.mixed p (secantResidualPoint c q r) =
      c.mixed r q * c.mixed p q - c.mixed q r * c.mixed p r := by
  rw [secantResidualPoint, show c.mixed r q • q - c.mixed q r • r =
      c.mixed r q • q + (-(c.mixed q r)) • r by
        simp only [sub_eq_add_neg, neg_smul],
    mixed_add_right, mixed_smul_right, mixed_smul_right]
  ring

/-- The secant residual of two points in a fixed tangent hyperplane remains
in that hyperplane. -/
theorem mixed_secantResidualPoint_eq_zero
    (c : Cubic R n) (p q r : Vec R n)
    (hq : c.mixed p q = 0) (hr : c.mixed p r = 0) :
    c.mixed p (secantResidualPoint c q r) = 0 := by
  rw [mixed_secantResidualPoint, hq, hr]
  ring

/-- Iterating tangent residuals and then a secant cannot leave the original
 tangent hyperplane. -/
theorem mixed_tangentSecantResidual_eq_zero
    (c : Cubic R n) (p d e : Vec R n)
    (hp : c.eval p = 0) (hd : c.mixed p d = 0) (he : c.mixed p e = 0) :
    c.mixed p (tangentSecantResidual c p d e) = 0 := by
  unfold tangentSecantResidual
  apply mixed_secantResidualPoint_eq_zero
  · exact mixed_tangentResidualPoint_eq_zero c p d hp hd
  · exact mixed_tangentResidualPoint_eq_zero c p e hp he

end
end Cubic
end PfaffianDescent

namespace PfaffianDescent
namespace Cubic

section

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Interchanging the two points on a secant line negates its residual
coordinates, so it does not change the resulting projective point. -/
theorem secantResidualPoint_swap (c : Cubic R n) (p q : Vec R n) :
    secantResidualPoint c q p = -secantResidualPoint c p q := by
  funext i
  simp only [secantResidualPoint, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

end

section

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- If a coefficient map exchanges two points, it sends their secant
residual coordinates to the negative residual coordinates in the original
ordering. -/
theorem map_secantResidualPoint_eq_neg_of_swap
    (f : R →+* S) (c : Cubic R n) (p0 q0 : Vec R n) (p q : Vec S n)
    (hfp : (fun i => f (p0 i)) = q) (hfq : (fun i => f (q0 i)) = p) :
    (fun i => f (secantResidualPoint c p0 q0 i)) =
      -secantResidualPoint (c.map f) p q := by
  rw [← map_secantResidualPoint f c p0 q0, hfp, hfq,
    secantResidualPoint_swap]

end

section

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The last secant operation in the two-conjugate-tangent construction is
anti-invariant under a coefficient automorphism that exchanges the two cubic
points and their tangent directions. -/
theorem map_twoTangentSecantResidual_eq_neg_of_conjugate
    (f : R →+* R) (c : Cubic R n) (p q dp dq : Vec R n)
    (hcf : c.map f = c)
    (hfp : (fun i => f (p i)) = q) (hfq : (fun i => f (q i)) = p)
    (hfdp : (fun i => f (dp i)) = dq) (hfdq : (fun i => f (dq i)) = dp) :
    (fun i => f (secantResidualPoint c
      (tangentResidualPoint c p dp) (tangentResidualPoint c q dq) i)) =
        -secantResidualPoint c
          (tangentResidualPoint c p dp) (tangentResidualPoint c q dq) := by
  rw [← map_secantResidualPoint f c
    (tangentResidualPoint c p dp) (tangentResidualPoint c q dq)]
  have htp : (fun i => f (tangentResidualPoint c p dp i)) =
      tangentResidualPoint c q dq := by
    rw [← map_tangentResidualPoint f c p dp, hcf, hfp, hfdp]
  have htq : (fun i => f (tangentResidualPoint c q dq i)) =
      tangentResidualPoint c p dp := by
    rw [← map_tangentResidualPoint f c q dq, hcf, hfq, hfdq]
  rw [hcf, htp, htq, secantResidualPoint_swap]

end
end Cubic
end PfaffianDescent

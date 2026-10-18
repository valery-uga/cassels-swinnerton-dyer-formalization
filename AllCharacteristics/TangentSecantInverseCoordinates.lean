import PfaffianDescent.CubicSecant

/-!
# Inverse coordinate identities for tangent sections and secant fibers

These identities hold in all
characteristics. They establish the coordinate inverse to projection from a
double point, and recover a secant endpoint by intersection with a hyperplane.
They do not assert generic tangent-section irreducibility or dominance.
-/

namespace PfaffianDescent.Cubic

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Restricting the quadratic first argument of the mixed coefficient to a
line, with its second argument equal to one endpoint. -/
theorem mixed_linearCombination_point
    (c : Cubic R n) (p d : Vec R n) (a b : R) :
    c.mixed (a • d + b • p) p =
      a ^ 2 * c.mixed d p + 2 * a * b * c.mixed p d +
        b ^ 2 * c.mixed p p := by
  simp only [mixed, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Tangent residual coordinates are invariant under translating the direction
by the tangency point, and scale cubically when the direction is scaled.
This is the coordinate identity making the construction descend to tangent
directions modulo the tangency point. -/
theorem tangentResidualPoint_linearCombination
    (c : Cubic R n) (p d : Vec R n) (a b : R)
    (hp : c.eval p = 0) (hd : c.mixed p d = 0) :
    tangentResidualPoint c p (a • d + b • p) =
      a ^ 3 • tangentResidualPoint c p d := by
  have hm : c.mixed (a • d + b • p) p = a ^ 2 * c.mixed d p := by
    rw [mixed_linearCombination_point, mixed_self_eq_three_eval, hp, hd]
    ring
  have he : c.eval (a • d + b • p) =
      a ^ 3 * c.eval d + a ^ 2 * b * c.mixed d p := by
    rw [eval_line, hp, hd]
    ring
  funext i
  simp only [tangentResidualPoint, hm, he, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Applying tangent projection to a point already on the tangent section
recovers that point in homogeneous coordinates. -/
theorem tangentResidualPoint_of_eval_zero
    (c : Cubic R n) (p x : Vec R n) (hx : c.eval x = 0) :
    tangentResidualPoint c p x = (-c.mixed x p) • x := by
  simp only [tangentResidualPoint, hx, zero_smul, zero_sub, neg_smul]

/-- On the tangent plane the cubic is linear in the coordinate along its
double point. This is the polynomial equation used for tangent projection. -/
theorem eval_tangentPlane_line
    (c : Cubic R n) (p d : Vec R n) (s : R)
    (hp : c.eval p = 0) (hd : c.mixed p d = 0) :
    c.eval (s • p + d) = s * c.mixed d p + c.eval d := by
  rw [show s • p + d = s • p + (1 : R) • d by rw [one_smul],
    eval_line, hp, hd]
  ring

/-- A cubic point of the tangent section fails the inverse-projection open
condition exactly when the entire joining line is contained in the cubic.
This equivalence is valid even over the smallest finite fields. -/
theorem mixed_reverse_eq_zero_iff_line_contained
    (c : Cubic R n) (p x : Vec R n)
    (hp : c.eval p = 0) (hx : c.eval x = 0)
    (ht : c.mixed p x = 0) :
    c.mixed x p = 0 ↔ ∀ s t : R, c.eval (s • p + t • x) = 0 := by
  constructor
  · intro hrev s t
    rw [eval_line, hp, hx, ht, hrev]
    ring
  · intro hline
    have h := hline 1 1
    rw [eval_line, hp, hx, ht] at h
    simpa only [one_pow, one_mul, mul_one, zero_add, add_zero] using h

/-- The direction from `p` to `x`, normalized into the hyperplane `ker ℓ`.
Its definition avoids division and is valid over every coefficient ring. -/
def projectionDirection (ℓ : Vec R n →ₗ[R] R) (p x : Vec R n) : Vec R n :=
  ℓ p • x - ℓ x • p

theorem projectionDirection_mem_ker
    (ℓ : Vec R n →ₗ[R] R) (p x : Vec R n) :
    projectionDirection ℓ p x ∈ LinearMap.ker ℓ := by
  change ℓ (ℓ p • x - ℓ x • p) = 0
  rw [ℓ.map_sub, ℓ.map_smul, ℓ.map_smul]
  simp only [smul_eq_mul]
  ring

/-- Normalizing a tangent-section point into any complementary hyperplane and
then taking its tangent residual recovers the original point, up to the
displayed homogeneous factor. -/
theorem tangentResidualPoint_projectionDirection
    (c : Cubic R n) (ℓ : Vec R n →ₗ[R] R) (p x : Vec R n)
    (hp : c.eval p = 0) (hx : c.eval x = 0)
    (ht : c.mixed p x = 0) :
    tangentResidualPoint c p (projectionDirection ℓ p x) =
      (-(ℓ p) ^ 3 * c.mixed x p) • x := by
  have hd : projectionDirection ℓ p x = ℓ p • x + (-ℓ x) • p := by
    simp only [projectionDirection, sub_eq_add_neg, neg_smul]
  rw [hd, tangentResidualPoint_linearCombination c p x (ℓ p) (-ℓ x) hp ht,
    tangentResidualPoint_of_eval_zero c p x hx, smul_smul]
  congr 1
  ring

/-- A secant endpoint in `ker ℓ` can be recovered from the residual point and
the other endpoint by intersecting the secant with `ker ℓ`. -/
theorem projectionDirection_secantResidualPoint
    (c : Cubic R n) (ℓ : Vec R n →ₗ[R] R) (u v : Vec R n)
    (hv : ℓ v = 0) :
    projectionDirection ℓ u (secantResidualPoint c u v) =
      (-(ℓ u) * c.mixed u v) • v := by
  have hl : ℓ (secantResidualPoint c u v) =
      c.mixed v u * ℓ u := by
    change ℓ (c.mixed v u • u - c.mixed u v • v) = c.mixed v u * ℓ u
    rw [ℓ.map_sub, ℓ.map_smul, ℓ.map_smul, hv]
    simp only [smul_eq_mul, mul_zero, sub_zero]
  funext i
  change ℓ u * (secantResidualPoint c u v i) -
    ℓ (secantResidualPoint c u v) * u i = (-(ℓ u) * c.mixed u v) * v i
  rw [hl]
  simp only [secantResidualPoint, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Ring

section Field

variable {K : Type*} [Field K] {n : ℕ}

/-- Tangent separation itself implies projective distinctness, so a separate
linear-independence premise is unnecessary for the residual secant map. -/
theorem linearIndependent_pair_of_mixed_reverse_ne_zero
    (c : Cubic K n) (p q : Vec K n)
    (hq : c.eval q = 0) (hsep : c.mixed q p ≠ 0) :
    LinearIndependent K ![p, q] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hzero
    change q = 0 at hzero
    apply hsep
    simp only [hzero, mixed, Pi.zero_apply, zero_mul, mul_zero,
      zero_add, add_zero, Finset.sum_const_zero]
  · intro a ha
    change a • q = p at ha
    apply hsep
    rw [← ha, mixed_smul_right, mixed_self_eq_three_eval, hq]
    ring

/-- The inverse tangent-projection identity has nonzero homogeneous
coordinates on its explicit open locus. -/
theorem tangentResidualPoint_projectionDirection_ne_zero
    (c : Cubic K n) (ℓ : Vec K n →ₗ[K] K) (p x : Vec K n)
    (hp : c.eval p = 0) (hx : c.eval x = 0)
    (ht : c.mixed p x = 0) (hℓ : ℓ p ≠ 0)
    (hxp : c.mixed x p ≠ 0) (hx0 : x ≠ 0) :
    tangentResidualPoint c p (projectionDirection ℓ p x) ≠ 0 := by
  rw [tangentResidualPoint_projectionDirection c ℓ p x hp hx ht]
  exact smul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 hℓ)) hxp) hx0

/-- When the secant is transverse and `u` avoids the endpoint hyperplane,
projection of the residual secant point recovers a nonzero endpoint. -/
theorem projectionDirection_secantResidualPoint_ne_zero
    (c : Cubic K n) (ℓ : Vec K n →ₗ[K] K) (u v : Vec K n)
    (hv : ℓ v = 0) (hℓ : ℓ u ≠ 0) (hsec : c.mixed u v ≠ 0)
    (hv0 : v ≠ 0) :
    projectionDirection ℓ u (secantResidualPoint c u v) ≠ 0 := by
  rw [projectionDirection_secantResidualPoint c ℓ u v hv]
  exact smul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hℓ) hsec) hv0

end Field

end PfaffianDescent.Cubic

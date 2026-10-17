import PfaffianDescent.Basic
import Mathlib.Tactic.LinearCombination

namespace PfaffianDescent
open scoped BigOperators

/-- Coefficients of a homogeneous cubic in finitely many coordinates.
Ordered triples allow repeated indices and represent every cubic form. -/
abbrev Cubic (R : Type*) (n : ℕ) := (Fin n × Fin n × Fin n) → R

namespace Cubic
section Ring
variable {R : Type*} [CommRing R] {n : ℕ}

/-- Evaluation of the homogeneous cubic in its coefficient ring. -/
def eval (c : Cubic R n) (x : Vec R n) : R :=
  ∑ i, c i * x i.1 * x i.2.1 * x i.2.2

/-- The coefficient of s²t in c(sa + tb). -/
def mixed (c : Cubic R n) (a b : Vec R n) : R :=
  ∑ i, c i * (a i.1 * a i.2.1 * b i.2.2 +
    a i.1 * b i.2.1 * a i.2.2 + b i.1 * a i.2.1 * a i.2.2)

private theorem term_expand (c s t a₀ a₁ a₂ b₀ b₁ b₂ : R) :
    c * (s*a₀+t*b₀) * (s*a₁+t*b₁) * (s*a₂+t*b₂) =
    s^3 * (c*a₀*a₁*a₂) + s^2*t * (c*(a₀*a₁*b₂+a₀*b₁*a₂+b₀*a₁*a₂)) +
    s*t^2 * (c*(b₀*b₁*a₂+b₀*a₁*b₂+a₀*b₁*b₂)) + t^3 * (c*b₀*b₁*b₂) := by
  ring

/-- The homogeneous binary cubic obtained by restricting to a line. -/
theorem eval_line (c : Cubic R n) (a b : Vec R n) (s t : R) :
    c.eval (s • a + t • b) = s^3 * c.eval a + s^2*t * c.mixed a b +
      s*t^2 * c.mixed b a + t^3 * c.eval b := by
  simp only [eval, mixed, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [term_expand, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem eval_smul (c : Cubic R n) (a : Vec R n) (s : R) :
    c.eval (s • a) = s^3 * c.eval a := by
  simp only [eval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem eval_zero (c : Cubic R n) : c.eval 0 = 0 := by
  simp only [eval, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

variable {S : Type*} [CommRing S]

/-- Change of coefficient ring for cubic forms. -/
def map (f : R →+* S) (c : Cubic R n) : Cubic S n := fun i => f (c i)

theorem eval_map (f : R →+* S) (c : Cubic R n) (x : Vec R n) :
    (c.map f).eval (fun i => f (x i)) = f (c.eval x) := by
  simp only [eval, map, map_sum, map_mul]

theorem mixed_map (f : R →+* S) (c : Cubic R n) (a b : Vec R n) :
    (c.map f).mixed (fun i => f (a i)) (fun i => f (b i)) = f (c.mixed a b) := by
  simp only [mixed, map, map_sum, map_mul, map_add]

/-- The explicit residual-root identity behind quadratic secant descent. -/
theorem residual_identity (a b c d r s : R)
    (h₀ : a + r*c + r*s*d = 0)
    (h₁ : b + s*c + (r+s^2)*d = 0) :
    d^3*a + d^2*(-(c+s*d))*b + d*(-(c+s*d))^2*c + (-(c+s*d))^3*d = 0 := by
  linear_combination d^3 * h₀ - d^2 * (c+s*d) * h₁

end Ring
end Cubic
end PfaffianDescent

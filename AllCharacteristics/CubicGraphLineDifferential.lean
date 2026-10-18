import AllCharacteristics.CubicContainedLineRigidity
import AllCharacteristics.CubicMultiplicity
import AllCharacteristics.CubicLineAlgebra
import PfaffianDescent.CubicSecant
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Actual differentiation of a cubic on a graph line.
The cubic coefficients belong to the ground field. Only the four graph
coordinates vary under a ground-field derivation.
-/

noncomputable section

namespace AllCharacteristics

open PfaffianDescent Polynomial
open scoped BigOperators

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Differentiating the actual cubic evaluation gives its mixed coefficient,
in every characteristic. -/
theorem cubic_derivation_eval
    {n : ℕ} (c : Cubic K n) (D : Derivation K L L) (x : Fin n → L) :
    D ((c.map (algebraMap K L)).eval x) =
      (c.map (algebraMap K L)).mixed x (fun i => D (x i)) := by
  unfold Cubic.eval Cubic.mixed Cubic.map
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [D.leibniz, D.map_algebraMap, smul_eq_mul, zero_mul, add_zero]
  ring

/-- The cross coefficient of the quadratic normal derivative along a line. -/
def cubicNormalCrossCoefficient {n : ℕ} (c : Cubic L n)
    (s b d : Fin n → L) : L :=
  ∑ i, c i *
    (s i.1 * b i.2.1 * d i.2.2 + b i.1 * s i.2.1 * d i.2.2 +
     s i.1 * d i.2.1 * b i.2.2 + b i.1 * d i.2.1 * s i.2.2 +
     d i.1 * s i.2.1 * b i.2.2 + d i.1 * b i.2.1 * s i.2.2)

private theorem cubic_normal_term_expand
    (c t s₀ s₁ s₂ b₀ b₁ b₂ d₀ d₁ d₂ : L) :
    c * ((t*s₀+b₀)*(t*s₁+b₁)*d₂ +
      (t*s₀+b₀)*d₁*(t*s₂+b₂) + d₀*(t*s₁+b₁)*(t*s₂+b₂)) =
    t^2 * (c * (s₀*s₁*d₂+s₀*d₁*s₂+d₀*s₁*s₂)) +
    t * (c * (s₀*b₁*d₂+b₀*s₁*d₂+s₀*d₁*b₂+b₀*d₁*s₂+d₀*s₁*b₂+d₀*b₁*s₂)) +
    c * (b₀*b₁*d₂+b₀*d₁*b₂+d₀*b₁*b₂) := by
  ring

theorem cubic_mixed_affine_line
    {n : ℕ} (c : Cubic L n) (s b d : Fin n → L) (t : L) :
    c.mixed (t • s + b) d =
      t^2 * c.mixed s d + t * cubicNormalCrossCoefficient c s b d + c.mixed b d := by
  simp only [Cubic.mixed, cubicNormalCrossCoefficient, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [cubic_normal_term_expand, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The actual normal derivative, as a quadratic polynomial in the affine
line parameter. -/
def cubicLineNormalPolynomial {n : ℕ} (c : Cubic L n) (s b d : Fin n → L) : L[X] :=
  C (c.mixed s d) * X^2 + C (cubicNormalCrossCoefficient c s b d) * X + C (c.mixed b d)

theorem cubicLineNormalPolynomial_eval
    {n : ℕ} (c : Cubic L n) (s b d : Fin n → L) (t : L) :
    (cubicLineNormalPolynomial c s b d).eval t = c.mixed (t • s + b) d := by
  rw [cubic_mixed_affine_line]
  simp only [cubicLineNormalPolynomial, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

theorem cubicLineNormalPolynomial_natDegree
    {n : ℕ} (c : Cubic L n) (s b d : Fin n → L) (h : c.mixed s d ≠ 0) :
    (cubicLineNormalPolynomial c s b d).natDegree = 2 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have hm1 : 1 ≠ m := by omega
    have hm2 : m ≠ 2 := by omega
    simp [cubicLineNormalPolynomial, coeff_C_mul, coeff_X, coeff_C, hm0, hm1, hm2]
  · simpa [cubicLineNormalPolynomial, coeff_C_mul] using h

/-- The two fixed graph coordinates are the line parameter and one. -/
def cubicGraphLineSlope (a : Fin 4 → L) : Fin 4 → L := ![1, 0, a 0, a 2]

def cubicGraphLineBase (a : Fin 4 → L) : Fin 4 → L := ![0, 1, a 1, a 3]

/-- Only the two normal components change when differentiating a graph line
at a ground-field value of its parameter. -/
theorem cubicGraphLine_derivation_point
    (a : Fin 4 → L) (D : Derivation K L L) (t : K) :
    (fun i => D ((algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a) i)) =
      ![0, 0, algebraMap K L t * D (a 0) + D (a 1),
        algebraMap K L t * D (a 2) + D (a 3)] := by
  funext i
  fin_cases i <;>
    simp [cubicGraphLineSlope, cubicGraphLineBase, D.leibniz,
      D.map_one_eq_zero, D.map_algebraMap, smul_eq_mul, Algebra.smul_def]

theorem cubic_mixed_two_normal_coordinates
    (c : Cubic L 4) (x : Fin 4 → L) (u v : L) :
    c.mixed x ![0, 0, u, v] =
      u * c.mixed x (Pi.single 2 1) + v * c.mixed x (Pi.single 3 1) := by
  have hvec : (![0, 0, u, v] : Fin 4 → L) =
      u • Pi.single 2 1 + v • Pi.single 3 1 := by
    funext i
    fin_cases i <;> simp [Pi.single_apply]
  rw [hvec, Cubic.mixed_add_right, Cubic.mixed_smul_right, Cubic.mixed_smul_right]

/-- Differentiate the actual graph containment identity. Infinitely many
ground-field values of the line parameter turn the resulting scalar
identities into a polynomial syzygy of the two actual normal quadratics. -/
theorem cubicGraphLine_derivation_normal_syzygy
    [Infinite K] (c : Cubic K 4) (a : Fin 4 → L)
    (hline : ∀ t : K, (c.map (algebraMap K L)).eval
      (algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a) = 0)
    (D : Derivation K L L) :
    let q := cubicLineNormalPolynomial (c.map (algebraMap K L))
      (cubicGraphLineSlope a) (cubicGraphLineBase a) (Pi.single 2 1)
    let r := cubicLineNormalPolynomial (c.map (algebraMap K L))
      (cubicGraphLineSlope a) (cubicGraphLineBase a) (Pi.single 3 1)
    (C (D (a 0)) * X + C (D (a 1))) * q +
      (C (D (a 2)) * X + C (D (a 3))) * r = 0 := by
  let q := cubicLineNormalPolynomial (c.map (algebraMap K L))
    (cubicGraphLineSlope a) (cubicGraphLineBase a) (Pi.single 2 1)
  let r := cubicLineNormalPolynomial (c.map (algebraMap K L))
    (cubicGraphLineSlope a) (cubicGraphLineBase a) (Pi.single 3 1)
  let f : L[X] := (C (D (a 0)) * X + C (D (a 1))) * q +
    (C (D (a 2)) * X + C (D (a 3))) * r
  change f = 0
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective (algebraMap K L).injective).mono
  rintro _ ⟨t, rfl⟩
  change f.eval (algebraMap K L t) = 0
  have hzero : D ((c.map (algebraMap K L)).eval
      (algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a)) = 0 := by
    rw [hline t, map_zero]
  rw [cubic_derivation_eval, cubicGraphLine_derivation_point,
    cubic_mixed_two_normal_coordinates] at hzero
  simpa only [f, q, r, eval_add, eval_mul, eval_C, eval_X,
    cubicLineNormalPolynomial_eval, mul_comm (algebraMap K L t)] using hzero

private theorem cubic_normal_linear_coefficients_eq_zero
    (q r : L[X]) (hq : q.natDegree = 2) (hqr : IsCoprime q r)
    (a b c d : L)
    (h : (C a * X + C b) * q + (C c * X + C d) * r = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hq0 : q ≠ 0 := by
    intro hzero
    simp only [hzero, Polynomial.natDegree_zero] at hq
    omega
  have hdiv : q ∣ (C c * X + C d) * r := by
    refine ⟨-(C a * X + C b), ?_⟩
    linear_combination h
  have hdiv' : q ∣ C c * X + C d := hqr.dvd_of_dvd_mul_right hdiv
  have hdeg : (C c * X + C d : L[X]).natDegree ≤ 1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : 1 ≠ n := by omega
    simp [coeff_C_mul, coeff_X, coeff_C, hn0, hn1]
  have hcd : (C c * X + C d : L[X]) = 0 := by
    by_contra hcd
    have hle := Polynomial.natDegree_le_of_dvd hdiv' hcd
    rw [hq] at hle
    omega
  have habq : (C a * X + C b) * q = 0 := by simpa only [hcd, zero_mul, add_zero] using h
  have hab := (mul_eq_zero.mp habq).resolve_right hq0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrArg (fun f : L[X] => f.coeff 1) hab
  · simpa using congrArg (fun f : L[X] => f.coeff 0) hab
  · simpa using congrArg (fun f : L[X] => f.coeff 1) hcd
  · simpa using congrArg (fun f : L[X] => f.coeff 0) hcd

/-- Actual graph containment plus the two normal-derivative smoothness
conditions forces all four graph coordinates to be killed by every scalar
derivation. The two conditions concern normal quadratics, not the desired
tangent-section geometry. -/
theorem cubicGraphLine_scalar_rigidity_of_normal_derivatives
    [Infinite K] (c : Cubic K 4) (a : Fin 4 → L)
    (hline : ∀ t : K, (c.map (algebraMap K L)).eval
      (algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a) = 0)
    (hcop : IsCoprime
      (cubicLineNormalPolynomial (c.map (algebraMap K L))
        (cubicGraphLineSlope a) (cubicGraphLineBase a) (Pi.single 2 1))
      (cubicLineNormalPolynomial (c.map (algebraMap K L))
        (cubicGraphLineSlope a) (cubicGraphLineBase a) (Pi.single 3 1)))
    (hinfty : (c.map (algebraMap K L)).mixed (cubicGraphLineSlope a) (Pi.single 2 1) ≠ 0 ∨
      (c.map (algebraMap K L)).mixed (cubicGraphLineSlope a) (Pi.single 3 1) ≠ 0)
    (D : Derivation K L L) : ∀ i, D (a i) = 0 := by
  let q := cubicLineNormalPolynomial (c.map (algebraMap K L))
    (cubicGraphLineSlope a) (cubicGraphLineBase a) (Pi.single 2 1)
  let r := cubicLineNormalPolynomial (c.map (algebraMap K L))
    (cubicGraphLineSlope a) (cubicGraphLineBase a) (Pi.single 3 1)
  have h := cubicGraphLine_derivation_normal_syzygy c a hline D
  have ha : D (a 0) = 0 ∧ D (a 1) = 0 ∧ D (a 2) = 0 ∧ D (a 3) = 0 := by
    rcases hinfty with hq | hr
    · exact cubic_normal_linear_coefficients_eq_zero q r
        (cubicLineNormalPolynomial_natDegree _ _ _ _ hq) hcop _ _ _ _ h
    · have h' : (C (D (a 2)) * X + C (D (a 3))) * r +
          (C (D (a 0)) * X + C (D (a 1))) * q = 0 := by
        simpa only [add_comm] using h
      obtain ⟨ha2, ha3, ha0, ha1⟩ := cubic_normal_linear_coefficients_eq_zero r q
        (cubicLineNormalPolynomial_natDegree _ _ _ _ hr) hcop.symm _ _ _ _ h'
      exact ⟨ha0, ha1, ha2, ha3⟩
  intro i
  fin_cases i
  · exact ha.1
  · exact ha.2.1
  · exact ha.2.2.1
  · exact ha.2.2.2

/-- Actual graph containment forces all four binary cubic coefficients to
vanish, even if the coordinate field is larger than the infinite ground field. -/
theorem cubicGraphLine_four_coefficients_eq_zero
    [Infinite K] (c : Cubic K 4) (a : Fin 4 → L)
    (hline : ∀ t : K, (c.map (algebraMap K L)).eval
      (algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a) = 0) :
    let cL := c.map (algebraMap K L)
    let s := cubicGraphLineSlope a
    let b := cubicGraphLineBase a
    cL.eval s = 0 ∧ cL.mixed s b = 0 ∧ cL.mixed b s = 0 ∧ cL.eval b = 0 := by
  let cL := c.map (algebraMap K L)
  let s := cubicGraphLineSlope a
  let b := cubicGraphLineBase a
  have hpoly : cubicLinePolynomial cL s b = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective (algebraMap K L).injective).mono
    rintro _ ⟨t, rfl⟩
    change (cubicLinePolynomial cL s b).eval (algebraMap K L t) = 0
    have heval := cubicLinePolynomial_eval₂ (RingHom.id L) cL s b (algebraMap K L t)
    simpa only [Polynomial.eval₂_id, Cubic.map, RingHom.id_apply] using heval.trans (hline t)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [cubicLinePolynomial, coeff_C_mul] using congrArg (fun f : L[X] => f.coeff 3) hpoly
  · simpa [cubicLinePolynomial, coeff_C_mul] using congrArg (fun f : L[X] => f.coeff 2) hpoly
  · simpa [cubicLinePolynomial, coeff_C_mul] using congrArg (fun f : L[X] => f.coeff 1) hpoly
  · simpa [cubicLinePolynomial, coeff_C_mul] using congrArg (fun f : L[X] => f.coeff 0) hpoly

/-- The graph slope and base, together with the two normal coordinate
vectors, span the entire four-dimensional ambient vector space. -/
theorem cubicGraphLine_mixed_eq_zero_of_four_frame_values
    (c : Cubic L 4) (a x : Fin 4 → L)
    (hs : c.mixed x (cubicGraphLineSlope a) = 0)
    (hb : c.mixed x (cubicGraphLineBase a) = 0)
    (h2 : c.mixed x (Pi.single 2 1) = 0)
    (h3 : c.mixed x (Pi.single 3 1) = 0) :
    ∀ d : Fin 4 → L, c.mixed x d = 0 := by
  intro d
  have hd : d = d 0 • cubicGraphLineSlope a + d 1 • cubicGraphLineBase a +
      (d 2 - d 0 * a 0 - d 1 * a 1) • Pi.single 2 1 +
      (d 3 - d 0 * a 2 - d 1 * a 3) • Pi.single 3 1 := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases i <;> simp [cubicGraphLineSlope, cubicGraphLineBase, Pi.single_apply] <;> ring
  rw [hd]
  simp only [Cubic.mixed_add_right, Cubic.mixed_smul_right, hs, hb, h2, h3, mul_zero, add_zero]

/-- Smoothness at the actual point at infinity supplies a nonzero leading
coefficient for one of the two normal quadratics. -/
theorem cubicGraphLine_nonzero_normal_at_infinity
    (c : Cubic L 4) (a : Fin 4 → L)
    (hs : c.eval (cubicGraphLineSlope a) = 0)
    (hsb : c.mixed (cubicGraphLineSlope a) (cubicGraphLineBase a) = 0)
    (hsmooth : ∃ d, c.mixed (cubicGraphLineSlope a) d ≠ 0) :
    c.mixed (cubicGraphLineSlope a) (Pi.single 2 1) ≠ 0 ∨
      c.mixed (cubicGraphLineSlope a) (Pi.single 3 1) ≠ 0 := by
  by_contra h
  push Not at h
  have hself : c.mixed (cubicGraphLineSlope a) (cubicGraphLineSlope a) = 0 := by
    rw [Cubic.mixed_self_eq_three_eval, hs, mul_zero]
  obtain ⟨d, hd⟩ := hsmooth
  exact hd (cubicGraphLine_mixed_eq_zero_of_four_frame_values c a _ hself hsb h.1 h.2 d)

theorem cubicNormalCrossCoefficient_last_slope
    (c : Cubic L 4) (s b : Fin 4 → L) :
    cubicNormalCrossCoefficient c s b s = 2 * c.mixed s b := by
  unfold cubicNormalCrossCoefficient Cubic.mixed
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cubicNormalCrossCoefficient_last_base
    (c : Cubic L 4) (s b : Fin 4 → L) :
    cubicNormalCrossCoefficient c s b b = 2 * c.mixed b s := by
  unfold cubicNormalCrossCoefficient Cubic.mixed
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- All tangential normal derivatives vanish on an actually contained line. -/
theorem cubicGraphLine_tangential_mixed_eq_zero
    (c : Cubic L 4) (s b : Fin 4 → L)
    (hcoeff : c.eval s = 0 ∧ c.mixed s b = 0 ∧ c.mixed b s = 0 ∧ c.eval b = 0)
    (t : L) :
    c.mixed (t • s + b) s = 0 ∧ c.mixed (t • s + b) b = 0 := by
  constructor
  · rw [cubic_mixed_affine_line, cubicNormalCrossCoefficient_last_slope,
      Cubic.mixed_self_eq_three_eval, hcoeff.1, hcoeff.2.1, hcoeff.2.2.1]
    ring
  · rw [cubic_mixed_affine_line, cubicNormalCrossCoefficient_last_base,
      Cubic.mixed_self_eq_three_eval, hcoeff.2.1, hcoeff.2.2.1, hcoeff.2.2.2]
    ring

theorem cubicNormalCrossCoefficient_map
    {M : Type u} [Field M] (f : L →+* M)
    (c : Cubic L 4) (s b d : Fin 4 → L) :
    cubicNormalCrossCoefficient (c.map f) (fun i => f (s i))
      (fun i => f (b i)) (fun i => f (d i)) =
      f (cubicNormalCrossCoefficient c s b d) := by
  simp only [cubicNormalCrossCoefficient, Cubic.map, map_sum, map_mul, map_add]

/-- Normal polynomials really are the scalar-extended normal derivatives at
all points over an arbitrary field extension. -/
theorem cubicLineNormalPolynomial_eval₂
    {M : Type u} [Field M] (f : L →+* M)
    (c : Cubic L 4) (s b d : Fin 4 → L) (t : M) :
    (cubicLineNormalPolynomial c s b d).eval₂ f t =
      (c.map f).mixed (t • (fun i => f (s i)) + (fun i => f (b i)))
        (fun i => f (d i)) := by
  rw [cubic_mixed_affine_line, Cubic.mixed_map, Cubic.mixed_map,
    cubicNormalCrossCoefficient_map]
  simp only [cubicLineNormalPolynomial, eval₂_add, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  ring

theorem cubicGraphLineSlope_map
    {M : Type u} [Field M] (f : L →+* M) (a : Fin 4 → L) :
    (fun i => f (cubicGraphLineSlope a i)) = cubicGraphLineSlope (fun i => f (a i)) := by
  funext i
  fin_cases i <;> simp [cubicGraphLineSlope]

theorem cubicGraphLineBase_map
    {M : Type u} [Field M] (f : L →+* M) (a : Fin 4 → L) :
    (fun i => f (cubicGraphLineBase a i)) = cubicGraphLineBase (fun i => f (a i)) := by
  funext i
  fin_cases i <;> simp [cubicGraphLineBase]

/-- The two normal quadratics on a contained graph line are coprime because
their common geometric root would be a singular point of the original cubic. -/
theorem cubicGraphLine_normalPolynomials_isCoprime_of_geometric_nonsingularity
    (c : Cubic L 4) (a : Fin 4 → L)
    (hcoeff : c.eval (cubicGraphLineSlope a) = 0 ∧
      c.mixed (cubicGraphLineSlope a) (cubicGraphLineBase a) = 0 ∧
      c.mixed (cubicGraphLineBase a) (cubicGraphLineSlope a) = 0 ∧
      c.eval (cubicGraphLineBase a) = 0)
    (hsmooth : ∀ (M : Type u) [Field M] (f : L →+* M) (x : Fin 4 → M),
      x ≠ 0 → (c.map f).eval x = 0 → ∃ d, (c.map f).mixed x d ≠ 0) :
    IsCoprime
      (cubicLineNormalPolynomial c (cubicGraphLineSlope a) (cubicGraphLineBase a) (Pi.single 2 1))
      (cubicLineNormalPolynomial c (cubicGraphLineSlope a) (cubicGraphLineBase a) (Pi.single 3 1)) := by
  let M := AlgebraicClosure L
  let f : L →+* M := algebraMap L M
  let aM : Fin 4 → M := fun i => f (a i)
  let cM := c.map f
  let s := cubicGraphLineSlope aM
  let b := cubicGraphLineBase aM
  have hcoeffM : cM.eval s = 0 ∧ cM.mixed s b = 0 ∧
      cM.mixed b s = 0 ∧ cM.eval b = 0 := by
    dsimp only [cM, s, b, aM]
    rw [← cubicGraphLineSlope_map f a, ← cubicGraphLineBase_map f a,
      Cubic.eval_map, Cubic.eval_map, Cubic.mixed_map, Cubic.mixed_map]
    simp only [hcoeff.1, hcoeff.2.1, hcoeff.2.2.1, hcoeff.2.2.2, map_zero, and_self]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed L M _ _).2
  intro t
  by_contra h
  push Not at h
  let x : Fin 4 → M := t • s + b
  have hx : x ≠ 0 := by
    intro hzero
    have h1 := congrFun hzero 1
    simpa [x, s, b, cubicGraphLineSlope, cubicGraphLineBase] using h1
  have hcx : cM.eval x = 0 := by
    change cM.eval (t • s + b) = 0
    rw [show t • s + b = t • s + (1 : M) • b by rw [one_smul]]
    rw [Cubic.eval_line, hcoeffM.1, hcoeffM.2.1, hcoeffM.2.2.1, hcoeffM.2.2.2]
    ring
  have htan := cubicGraphLine_tangential_mixed_eq_zero cM s b hcoeffM t
  have heval (j : Fin 4) :
      Polynomial.aeval t (cubicLineNormalPolynomial c (cubicGraphLineSlope a)
        (cubicGraphLineBase a) (Pi.single j (1 : L))) = cM.mixed x (Pi.single j (1 : M)) := by
    rw [Polynomial.aeval_def, cubicLineNormalPolynomial_eval₂]
    rw [cubicGraphLineSlope_map, cubicGraphLineBase_map]
    have hsingle : (fun i : Fin 4 => f ((Pi.single j (1 : L) : Fin 4 → L) i)) =
        (Pi.single j (1 : M) : Fin 4 → M) := by
      funext i
      simp [Pi.single_apply, apply_ite]
    rw [hsingle]
  have h2 : cM.mixed x (Pi.single 2 1) = 0 := by rw [← heval 2]; exact h.1
  have h3 : cM.mixed x (Pi.single 3 1) = 0 := by rw [← heval 3]; exact h.2
  obtain ⟨d, hd⟩ := hsmooth M f x hx hcx
  exact hd (cubicGraphLine_mixed_eq_zero_of_four_frame_values cM aM x htan.1 htan.2 h2 h3 d)

end AllCharacteristics

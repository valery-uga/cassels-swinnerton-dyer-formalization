import AllCharacteristics.UniversalSecantPolynomialDescent
import AllCharacteristics.UniversalSecantPolynomialCubic

namespace PfaffianDescent

open MvPolynomial

universe u v

/-- The exact scalar descent of a polynomial cubic point still satisfies the
cubic over the original coefficient field. -/
theorem eval_descended_polynomial_cubic_point_eq_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type v} {n : ℕ} (c : Cubic K n)
    (r : Fin n → MvPolynomial ι L) (R : Fin n → MvPolynomial ι K) (s : L)
    (hR : ∀ i, MvPolynomial.map (algebraMap K L) (R i) = MvPolynomial.C s * r i)
    (hr : ((c.map (algebraMap K L)).map MvPolynomial.C).eval r = 0) :
    (c.map MvPolynomial.C).eval R = 0 := by
  let μ : MvPolynomial ι K →+* MvPolynomial ι L := MvPolynomial.map (algebraMap K L)
  let cP := c.map (MvPolynomial.C : K →+* MvPolynomial ι K)
  have hc : cP.map μ = (c.map (algebraMap K L)).map MvPolynomial.C := by
    funext i
    simp [cP, Cubic.map, μ]
  have hvec : (fun i => μ (R i)) = (MvPolynomial.C s : MvPolynomial ι L) • r := by
    funext i
    exact hR i
  apply MvPolynomial.map_injective (algebraMap K L) (algebraMap K L).injective
  rw [map_zero]
  have hmap := Cubic.eval_map μ cP R
  rw [hc, hvec, Cubic.eval_smul, hr, mul_zero] at hmap
  exact hmap.symm

/-- A zero descended polynomial vector would force the raw vector to be
zero, since the retained descent scalar is nonzero. -/
theorem descended_polynomial_vector_ne_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ι : Type v} {n : ℕ}
    (r : Fin n → MvPolynomial ι L) (R : Fin n → MvPolynomial ι K) (s : L)
    (hs : s ≠ 0) (hr : r ≠ 0)
    (hR : ∀ i, MvPolynomial.map (algebraMap K L) (R i) = MvPolynomial.C s * r i) :
    R ≠ 0 := by
  intro hzero
  apply hr
  funext i
  have hi := hR i
  rw [hzero] at hi
  have hprod : MvPolynomial.C s * r i = 0 := by simpa only [Pi.zero_apply, map_zero] using hi.symm
  exact (mul_eq_zero.mp hprod).resolve_left (by simpa only [ne_eq, MvPolynomial.C_eq_zero] using hs)

/-- Any injective evaluation of the actual coefficient polynomial ring keeps
the descended homogeneous vector nonzero and on its cubic. -/
theorem mapped_polynomial_cubic_point
    {K E : Type u} [Field K] [Field E]
    {ι : Type v} {n : ℕ}
    (f : MvPolynomial ι K →+* E) (hf : Function.Injective f)
    (c : Cubic K n) (R : Fin n → MvPolynomial ι K)
    (hR : R ≠ 0) (hc : (c.map MvPolynomial.C).eval R = 0) :
    (fun i => f (R i)) ≠ 0 ∧
      (c.map (f.comp MvPolynomial.C)).eval (fun i => f (R i)) = 0 := by
  constructor
  · intro hzero
    apply hR
    funext i
    apply hf
    have hi := congrFun hzero i
    simpa only [Pi.zero_apply, map_zero] using hi
  · have h := Cubic.eval_map f (c.map MvPolynomial.C) R
    rw [hc, map_zero] at h
    exact h

end PfaffianDescent

import PfaffianDescent.VoisinIntrinsicQuadraticKernelIdeal

/-! Equality of intrinsic ideals from matching chart-coordinate ratios. -/

namespace PfaffianDescent

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Matching normalized ratios of eight labeled nonzero vectors are enough
to identify their intrinsic cubic-plus-quadratic-kernel ideals. -/
theorem intrinsicEightPointTripleHomogeneousIdeal_eq_of_ratioFamilies
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (x y : Fin 8 → Fin 4 → F)
    (j : Fin 8 → Fin 4)
    (hxj : ∀ k, x k (j k) ≠ 0)
    (hratio : ∀ k i,
      (y k (j k))⁻¹ * y k i = (x k (j k))⁻¹ * x k i) :
    intrinsicEightPointTripleHomogeneousIdeal p hp y =
      intrinsicEightPointTripleHomogeneousIdeal p hp x := by
  have hyj : ∀ k, y k (j k) ≠ 0 := by
    intro k hk
    have h := hratio k (j k)
    simp [hk, hxj k] at h
  let a : Fin 8 → F := fun k => y k (j k) / x k (j k)
  have ha : ∀ k, IsUnit (a k) := by
    intro k
    exact isUnit_iff_ne_zero.mpr (div_ne_zero (hyj k) (hxj k))
  have hscale : y = fun k i => a k * x k i := by
    funext k i
    calc
      y k i = y k (j k) * ((y k (j k))⁻¹ * y k i) := by simp [hyj k]
      _ = y k (j k) * ((x k (j k))⁻¹ * x k i) := by rw [hratio k i]
      _ = a k * x k i := by simp only [a, div_eq_mul_inv, mul_assoc]
  rw [hscale]
  simpa only [Equiv.refl_apply] using
    intrinsicEightPointTripleHomogeneousIdeal_scale_relabel
      p hp (Equiv.refl (Fin 8)) a ha x

end PfaffianDescent

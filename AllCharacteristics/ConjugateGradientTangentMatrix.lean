import AllCharacteristics.ConjugateUniversalTangentCoordinates

namespace AllCharacteristics

open PfaffianDescent MvPolynomial

universe u

/-- A gradient coordinate is the tangent pairing against its coordinate
vector, so its automorphic transformation can be read from the cubic tensor. -/
theorem cubic_pderiv_eval_eq_mixed_single
    {L : Type u} [Field L] (c : Cubic L 4) (x : Fin 4 → L) (i : Fin 4) :
    (MvPolynomial.pderiv i c.toMvPolynomial).eval x = c.mixed x (Pi.single i 1) := by
  rw [Cubic.mixed_eq_sum_pderiv_eval]
  simp [Pi.single_apply]

/-- Conjugating a point conjugates its gradient when the cubic is fixed. -/
theorem cubic_gradient_conjugate_of_fixed
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (c : Cubic L 4) (hc : c.map σ.toRingHom = c)
    (x : Fin 4 → L) :
    (fun i => σ ((MvPolynomial.pderiv i c.toMvPolynomial).eval x)) =
      fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval (fun j => σ (x j)) := by
  funext i
  rw [cubic_pderiv_eval_eq_mixed_single, cubic_pderiv_eval_eq_mixed_single]
  have hsingle : (fun j => σ.toRingHom ((Pi.single i 1 : Fin 4 → L) j)) = Pi.single i 1 := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.single_apply, hji, Ne.symm hji]
  have h := Cubic.mixed_map σ.toRingHom c x (Pi.single i 1)
  rw [hc, hsingle] at h
  change c.mixed (fun j => σ (x j)) (Pi.single i 1) = σ (c.mixed x (Pi.single i 1)) at h
  exact h.symm

/-- The conjugate tangent matrix is exactly the explicit gradient matrix at
the conjugate center, with the same pivot. -/
theorem hyperplaneInclusion_gradient_conjugate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (c : Cubic L 4) (hc : c.map σ.toRingHom = c)
    (x : Fin 4 → L) (k : Fin 4) :
    (hyperplaneInclusion
      (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval x) k).map σ =
      hyperplaneInclusion
        (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval (fun j => σ (x j))) k := by
  change (hyperplaneInclusion
    (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval x) k).map σ.toRingHom = _
  rw [map_hyperplaneInclusion]
  change hyperplaneInclusion
    (fun i => σ ((MvPolynomial.pderiv i c.toMvPolynomial).eval x)) k = _
  exact congrArg (fun g : Fin 4 → L => hyperplaneInclusion g k)
    (cubic_gradient_conjugate_of_fixed σ c hc x)

/-- A nonzero gradient pivot remains nonzero at the conjugate center. -/
theorem gradient_conjugate_pivot_ne_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (c : Cubic L 4) (hc : c.map σ.toRingHom = c)
    (x : Fin 4 → L) (k : Fin 4)
    (hk : (MvPolynomial.pderiv k c.toMvPolynomial).eval x ≠ 0) :
    (MvPolynomial.pderiv k c.toMvPolynomial).eval (fun j => σ (x j)) ≠ 0 := by
  intro hzero
  apply hk
  apply σ.injective
  rw [map_zero]
  exact (congrFun (cubic_gradient_conjugate_of_fixed σ c hc x) k).trans hzero

end AllCharacteristics

import AllCharacteristics.ValuationSpecialization
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Specialization of arbitrary projective homogeneous equations

The coefficient objects are Mathlib multivariate polynomials. Consequently the
result applies to projective hypersurfaces without assuming a particular tensor
or Pfaffian presentation, and simultaneously to families of homogeneous equations.
-/

namespace AllCharacteristics

section Homogeneity
variable {R S ι : Type*} [CommSemiring R] [CommSemiring S]

/-- Scaling the coordinates of a homogeneous polynomial scales its value by the
corresponding power. This also includes degree zero and the zero polynomial. -/
theorem eval₂_homogeneous_smul (p : MvPolynomial ι R) {d : ℕ}
    (hp : p.IsHomogeneous d) (f : R →+* S) (x : ι → S) (c : S) :
    p.eval₂ f (c • x) = c ^ d * p.eval₂ f x := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support hm]
  ac_rfl

end Homogeneity

section Specialization
variable {R K k ι : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [CommRing k] [Nontrivial k] [Fintype ι]

/-- A common zero of any family of homogeneous equations over the fraction
field specializes to a nonzero common zero after reduction. The equations may
have different degrees. -/
theorem specialize_homogeneous_equations {J : Type*}
    (p : J → MvPolynomial ι R) (d : J → ℕ)
    (hp : ∀ j, (p j).IsHomogeneous (d j)) (red : R →+* k)
    (x : ι → K) (hx : x ≠ 0)
    (hpx : ∀ j, (p j).eval₂ (algebraMap R K) x = 0) :
    ∃ y : ι → k, y ≠ 0 ∧ ∀ j, (p j).eval₂ red y = 0 := by
  obtain ⟨y, c, _, hy, i, hi⟩ := normalize_fraction_coordinates (R := R) x hx
  have hpy : ∀ j, MvPolynomial.eval y (p j) = 0 := by
    intro j
    apply IsFractionRing.injective R K
    rw [map_zero, MvPolynomial.eval₂_comp]
    change (p j).eval₂ (algebraMap R K) (fun i => algebraMap R K (y i)) = 0
    rw [hy, eval₂_homogeneous_smul (p j) (hp j), hpx j, mul_zero]
  refine ⟨fun j => red (y j), ?_, ?_⟩
  · intro hz
    have hz' := congrFun hz i
    exact one_ne_zero (by simpa only [hi, map_one, Pi.zero_apply] using hz')
  · intro j
    change (p j).eval₂ red (red ∘ y) = 0
    rw [← MvPolynomial.eval₂_comp, hpy j, map_zero]

/-- The hypersurface case, directly for a multivariate homogeneous equation. -/
theorem specialize_homogeneous_polynomial (p : MvPolynomial ι R) {d : ℕ}
    (hp : p.IsHomogeneous d) (red : R →+* k)
    (x : ι → K) (hx : x ≠ 0) (hpx : p.eval₂ (algebraMap R K) x = 0) :
    ∃ y : ι → k, y ≠ 0 ∧ p.eval₂ red y = 0 := by
  obtain ⟨y, hy, hpy⟩ := specialize_homogeneous_equations
    (fun _ : Unit => p) (fun _ => d) (fun _ => hp) red x hx (fun _ => hpx)
  exact ⟨y, hy, hpy ()⟩

end Specialization
end AllCharacteristics

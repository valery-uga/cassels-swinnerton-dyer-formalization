import AllCharacteristics.SmoothCubicJacobianProjectiveEmpty
import AllCharacteristics.ProjectivePoints
import Mathlib.Tactic

/-! SOURCE ONLY / UNVERIFIED. Smoothness excludes vanishing to order two
along any nonzero field-valued projective vector. This supplies the exact
nonvanishing input needed for the mixed secant pieces; a final theorem
must derive their membership in the squared line ideal explicitly. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SmoothNonvanishing
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra
variable {k L : Type u} [Field k] [Field L]

/-- All first derivatives vanish when an equation belongs to the square
of an ideal vanishing at the chosen field-valued vector. -/
theorem eval_and_partials_zero_of_mem_square
    (f : k →+* L) (x : Fin 4 → L)
    (I : Ideal (MvPolynomial (Fin 4) k))
    (hI : ∀ a ∈ I, a.eval₂ f x = 0)
    (p : MvPolynomial (Fin 4) k) (hp : p ∈ I ^ 2) :
    p.eval₂ f x = 0 ∧ ∀ j, (pderiv j p).eval₂ f x = 0 := by
  have hp' : p ∈ I * I := by simpa only [pow_two] using hp
  refine Submodule.mul_induction_on hp' ?_ ?_
  · intro a ha b hb
    constructor
    · rw [eval₂_mul, hI a ha, zero_mul]
    · intro j
      rw [pderiv_mul, eval₂_add, eval₂_mul, eval₂_mul, hI a ha, hI b hb]
      simp only [mul_zero, zero_mul, add_zero]
  · intro a b ha hb
    constructor
    · rw [eval₂_add, ha.1, hb.1, add_zero]
    · intro j
      rw [map_add, eval₂_add, ha.2 j, hb.2 j, add_zero]

end Algebra

/-- This necessary Jacobian direction is derived from the actual smooth
original cubic, over any residue field. -/
theorem smooth_original_cubic_exists_nonzero_partial
    {k L : Type u} [Field k] [Field L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hp₀ : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (f : k →+* L) (x : Fin 4 → L) (hx : x ≠ 0)
    (hpx : p.eval₂ f x = 0) :
    ∃ j, (pderiv j p).eval₂ f x ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  let J := cubicJacobianIdeal p hp
  have hle : J.toIdeal ≤ RingHom.ker (MvPolynomial.eval₂Hom f x) := by
    simp only [J, cubicJacobianIdeal, HomogeneousIdeal.toIdeal_sup,
      HomogeneousIdeal.toIdeal_iSup]
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro q rfl
      exact hpx
    · refine iSup_le fun j => ?_
      apply Ideal.span_le.mpr
      rintro q rfl
      exact h j
  obtain ⟨q, _⟩ := point_of_coordinates J f x hx (fun a ha => hle ha)
  letI : IsEmpty (scheme J) := smoothCubic_cubicJacobianScheme_isEmpty p hp hp₀
  exact isEmptyElim (q (IsLocalRing.closedPoint L))

/-- In particular, the two mixed secant coefficients cannot disappear
by making the cubic vanish doubly on an actual contained line. -/
theorem smooth_original_cubic_not_mem_square
    {k L : Type u} [Field k] [Field L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hp₀ : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (f : k →+* L) (x : Fin 4 → L) (hx : x ≠ 0)
    (I : Ideal (MvPolynomial (Fin 4) k))
    (hI : ∀ a ∈ I, a.eval₂ f x = 0) :
    p ∉ I ^ 2 := by
  intro hmem
  obtain ⟨hpx, hpartials⟩ := eval_and_partials_zero_of_mem_square f x I hI p hmem
  obtain ⟨j, hj⟩ := smooth_original_cubic_exists_nonzero_partial p hp hp₀ f x hx hpx
  exact hj (hpartials j)

end PfaffianDescent.QuadraticSkewRationality.SmoothNonvanishing

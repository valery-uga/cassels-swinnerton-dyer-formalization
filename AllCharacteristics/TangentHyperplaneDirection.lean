import AllCharacteristics.TangentHyperplaneGeneric

/-!
# Non-cubic directions in a tangent hyperplane

Over an infinite field, a smooth cubic surface has a tangent-hyperplane
direction at each smooth coordinate point that is not itself on the cubic.
This gives a genuine residual tangent point over the field, complementing the
function-field generic-direction construction.
-/

namespace AllCharacteristics

open AlgebraicGeometry
open HomogeneousProjective
open PfaffianDescent MvPolynomial

universe u

/-- Restricting a cubic to matrix-defined linear coordinates and then
specializing is the same as evaluating it at the matrix-vector product. -/
theorem cubic_eval_matrix_mulVec
    {K : Type u} [Field K] (c : Cubic K 4)
    (M : Matrix (Fin 4) (Fin 3) K) (u : Fin 3 → K) :
    c.eval (M.mulVec u) = (rectangularSubstitution M c.toMvPolynomial).eval u := by
  have hcomp : MvPolynomial.eval₂Hom (RingHom.id K) (M.mulVec u) =
      (MvPolynomial.eval u).comp (rectangularSubstitution M).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
      change M.mulVec u i = MvPolynomial.eval u
        (rectangularSubstitution M (MvPolynomial.X i))
      rw [rectangularSubstitution_X]
      change M.mulVec u i = MvPolynomial.eval₂ (RingHom.id K) u
        (rectangularLinearCoordinate M i)
      rw [eval₂_rectangularLinearCoordinate]
      rfl
  have he := DFunLike.congr_fun hcomp c.toMvPolynomial
  change MvPolynomial.eval₂ (RingHom.id K) (M.mulVec u) c.toMvPolynomial =
    MvPolynomial.eval u (rectangularSubstitution M c.toMvPolynomial) at he
  rw [Cubic.eval_toMvPolynomial] at he
  have hmap : c.map (RingHom.id K) = c := by
    funext t
    rfl
  rw [hmap] at he
  exact he

/-- A smooth cubic point over an infinite field has a tangent direction whose
cubic value is nonzero. -/
theorem exists_tangent_direction_with_eval_ne_zero_of_smooth_of_infinite
    {K : Type u} [Field K] [Infinite K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    (p : Fin 4 → K) (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ d : Fin 4 → K, c.mixed p d = 0 ∧ c.eval d ≠ 0 := by
  classical
  obtain ⟨-, -, k, hk⟩ := hs
  let g : Fin 4 → K := fun i ↦ (MvPolynomial.pderiv i c.toMvPolynomial).eval p
  have hg : ∀ i, g i = (MvPolynomial.pderiv i c.toMvPolynomial).eval p := by
    intro i
    rfl
  have hgk : g k ≠ 0 := by
    simpa only [g] using hk
  have hF0 : F ≠ 0 := by
    intro hzero
    apply hk
    rw [hc, hzero]
    simp
  have hprime : (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic F hF hF0
  let M := hyperplaneInclusion g k
  have hrestF : rectangularSubstitution M F ≠ 0 :=
    hyperplane_restriction_ne_zero_of_prime F hF hF0 hprime g k hgk
  have hrest : rectangularSubstitution M c.toMvPolynomial ≠ 0 := by
    rw [hc]
    exact hrestF
  have hresthom : (rectangularSubstitution M c.toMvPolynomial).IsHomogeneous 3 := by
    rw [hc]
    exact rectangularSubstitution_homogeneous M hF
  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → K,
      (rectangularSubstitution M c.toMvPolynomial).eval u ≠ 0 := by
    by_contra h
    push Not at h
    apply hrest
    exact hresthom.eq_zero_of_forall_eval_eq_zero h
  let d : Fin 4 → K := M.mulVec u
  refine ⟨d, ?_, ?_⟩
  · exact mixed_hyperplaneInclusion_zero (RingHom.id K) c p g hg k hgk u
  · change c.eval (M.mulVec u) ≠ 0
    rw [cubic_eval_matrix_mulVec]
    exact hu

end AllCharacteristics

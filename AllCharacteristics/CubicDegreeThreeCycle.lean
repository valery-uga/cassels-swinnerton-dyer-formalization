import AllCharacteristics.CubicLineAlgebra
import AllCharacteristics.ProjectiveRingPoints
import AllCharacteristics.ProperCyclePushforward
import AllCharacteristics.EffectiveCycleToZeroCycle
import PfaffianDescent.CubicLineFiniteSubscheme
import PfaffianDescent.SectionCycles

/-!
# Actual degree-three cycles on cubic hypersurfaces

A rational coordinate point supplies a triple point cycle. Otherwise the line
through two coordinate points has a finite intersection algebra of dimension
three. Its unit-coordinate solution gives a point of the actual projective
hypersurface, and pushforward of the fundamental cycle has degree three.
This construction works over every field, including finite and imperfect fields.
-/

open AlgebraicGeometry CategoryTheory PfaffianDescent
namespace AllCharacteristics
namespace HomogeneousProjective
universe u

/-- Every projective cubic hypersurface with at least two coordinate indices
has an actual effective zero-cycle of degree three, over every field. -/
theorem hypersurface_exists_effective_degree_three
    {k : Type u} [Field k] {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 3 := by
  classical
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor_any_characteristic p hp
  by_cases hi : c.eval (Pi.single i 1) = 0
  · have he : p.eval₂ (RingHom.id k) (Pi.single i 1) = 0 := by
      rw [← hc, Cubic.eval_toMvPolynomial]
      exact hi
    obtain ⟨q, hq⟩ := hypersurface_point_of_unit_coordinates (RingHom.id k) p hp
      (Pi.single i 1) i (by simp) he
    have hqid : q ≫ hypersurfaceToBase p hp = 𝟙 _ := by simpa using hq
    exact PfaffianDescent.effective_cycle_of_section (hypersurfaceToBase p hp) q hqid 3
  · obtain ⟨A, _, _, _, hd, x, hx, he⟩ := cubic_rank_three_algebra_solution i j hij c hi
    have he' : p.eval₂ (algebraMap k A) x = 0 := by
      rw [← hc, Cubic.eval_toMvPolynomial]
      exact he
    obtain ⟨q, hq⟩ := hypersurface_point_of_unit_coordinates (algebraMap k A) p hp x j
      (hx.symm ▸ isUnit_one) he'
    obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_algebra_point
      (hypersurfaceToBase p hp) q hq
    exact ⟨z, hz.trans hd⟩

/-- Over an infinite field, the degree-three reference cycle can be taken to
be the intrinsic fundamental cycle of an actual finite line section. -/
theorem hypersurface_exists_lineSection_effective_degree_three
    {k : Type u} [Field k] [Infinite k] {n : ℕ} (hn : 2 ≤ n)
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 3 :=
  ⟨PfaffianDescent.cubicLineSectionCycle hn p hp hp0,
    PfaffianDescent.cubicLineSectionCycle_degree hn p hp hp0⟩

/-- Every projective cubic hypersurface with two distinct coordinate indices
has an actual integer zero-cycle of degree three. -/
theorem hypersurface_exists_zeroCycle_degree_three
    {k : Type u} [Field k] {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3) :
    ∃ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 3 := by
  obtain ⟨z, hz⟩ := hypersurface_exists_effective_degree_three i j hij p hp
  refine ⟨z.toZeroCycle, ?_⟩
  rw [EffectiveZeroCycle.degree_toZeroCycle, hz]
  rfl

/-- On an actual projective cubic surface, a closed point of degree prime to
three gives a signed zero-cycle of degree one. The degree-three cycle is
constructed, rather than supplied as an additional hypothesis. -/
theorem cubicSurface_zeroCycle_degree_one_of_coprime_closedPoint
    {k : Type u} [Field k] (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) :
    ∃ z : ZeroCycle (hypersurface p hp), ZeroCycle.degree (hypersurfaceToBase p hp) z = 1 := by
  obtain ⟨z₃, hz₃⟩ := hypersurface_exists_zeroCycle_degree_three 0 1 (by decide) p hp
  exact ZeroCycle.exists_degree_one_of_coprime (hypersurfaceToBase p hp) z₃ hz₃ x hx

/-- A finite closed subscheme of rank prime to three on an actual projective
cubic surface gives a signed degree-one cycle over every field. -/
theorem cubicSurface_zeroCycle_degree_one_of_coprime_finite_subscheme
    {k : Type u} [Field k] (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : Nat.Coprime (finiteSchemeRank (i ≫ hypersurfaceToBase p hp)) 3) :
    ∃ z : ZeroCycle (hypersurface p hp), ZeroCycle.degree (hypersurfaceToBase p hp) z = 1 := by
  obtain ⟨z₃, hz₃⟩ := hypersurface_exists_zeroCycle_degree_three 0 1 (by decide) p hp
  exact degree_one_cycle_of_finite_closed_subscheme i (hypersurfaceToBase p hp) hi z₃ hz₃

/-- For an actual projective cubic surface over any field, existence of a
signed degree-one cycle is equivalent to existence of a closed point whose
full residue degree is prime to three. -/
theorem cubicSurface_zeroCycle_degree_one_iff_coprime_closedPoint
    {k : Type u} [Field k] (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    (∃ z : ZeroCycle (hypersurface p hp), ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) ↔
      ∃ x : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3 := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨x, _, hx⟩ := ZeroCycle.exists_coprime_degree (hypersurfaceToBase p hp) z hz
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact cubicSurface_zeroCycle_degree_one_of_coprime_closedPoint p hp x hx

end HomogeneousProjective
end AllCharacteristics

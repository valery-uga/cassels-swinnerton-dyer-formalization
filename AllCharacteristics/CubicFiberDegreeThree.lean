import AllCharacteristics.CubicDegreeThreeCycle
import AllCharacteristics.ProjectiveFiberRingPoints
import AllCharacteristics.FiniteFlatCycle

/-!
# Degree-three cycles and Bézout on actual cubic fibers

The line-intersection construction applies directly to pullback fibers, using
unit-coordinate solutions over finite algebras. Thus an actual finite flat
closed subscheme of rank prime to three supplies a signed degree-one cycle on
every field-valued fiber of the cubic family. No Proj base-change isomorphism,
separability hypothesis, or pre-existing degree-three cycle is assumed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PfaffianDescent
namespace AllCharacteristics
open HomogeneousProjective
universe u

/-- Every field-valued fiber of a cubic hypersurface with two distinct
coordinate indices has an actual effective cycle of degree three. -/
theorem hypersurface_fiber_exists_effective_degree_three
    {R k : Type u} [CommRing R] [Field k] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j)
    (p : MvPolynomial (Fin n) R) (hp : p.IsHomogeneous 3) (b : R →+* k) :
    ∃ z : EffectiveZeroCycle
        (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))),
      EffectiveZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z = 3 := by
  classical
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor_any_characteristic (p.map b) (hp.map b)
  by_cases hi : c.eval (Pi.single i 1) = 0
  · have he : p.eval₂ b (Pi.single i 1) = 0 := by
      rw [MvPolynomial.eval₂_eq_eval_map, ← hc]
      change MvPolynomial.eval₂ (RingHom.id k) (Pi.single i 1) c.toMvPolynomial = 0
      rw [Cubic.eval_toMvPolynomial]
      exact hi
    obtain ⟨q, hq⟩ := (hypersurface_fiber_section_iff_coordinates p hp b).mpr
      ⟨Pi.single i 1, by simp, he⟩
    exact PfaffianDescent.effective_cycle_of_section
      (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) q hq 3
  · obtain ⟨A, _, _, _, hd, x, hx, he⟩ := cubic_rank_three_algebra_solution i j hij c hi
    have he' : (p.map b).eval₂ (algebraMap k A) x = 0 := by
      rw [← hc, Cubic.eval_toMvPolynomial]
      exact he
    obtain ⟨z, hz⟩ := hypersurface_fiber_cycle_of_finite_algebra_solution p hp b
      x j (hx.symm ▸ isUnit_one) he'
    exact ⟨z, hz.trans hd⟩

/-- The actual pullback fiber has a signed degree-three cycle over its field
of definition, in every characteristic. -/
theorem hypersurface_fiber_exists_zeroCycle_degree_three
    {R k : Type u} [CommRing R] [Field k] {n : ℕ}
    (i j : Fin n) (hij : i ≠ j)
    (p : MvPolynomial (Fin n) R) (hp : p.IsHomogeneous 3) (b : R →+* k) :
    ∃ z : ZeroCycle
        (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))),
      ZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z = 3 := by
  obtain ⟨z, hz⟩ := hypersurface_fiber_exists_effective_degree_three i j hij p hp b
  refine ⟨z.toZeroCycle, ?_⟩
  rw [EffectiveZeroCycle.degree_toZeroCycle, hz]
  rfl

/-- An actual finite flat closed subscheme of rank prime to three supplies a
signed degree-one cycle on each field-valued fiber of the cubic family. The
required degree-three cycle is constructed inside that same pullback fiber. -/
theorem cubic_finite_flat_fiber_exists_zeroCycle_degree_one
    {R k : Type u} [CommRing R] [IsLocalRing R] [Field k]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] [Flat (i ≫ hypersurfaceToBase p hp)]
    [LocallyOfFinitePresentation (i ≫ hypersurfaceToBase p hp)]
    (hi : Nat.Coprime
      ((i ≫ hypersurfaceToBase p hp).finrank (IsLocalRing.closedPoint R)) 3)
    (b : R →+* k) :
    ∃ z : ZeroCycle
        (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))),
      ZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z = 1 := by
  let f := pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))
  obtain ⟨w, hw⟩ := exists_effectiveZeroCycle_ambient_fiber i (hypersurfaceToBase p hp)
    (Spec.map (CommRingCat.ofHom b))
  have hc : Nat.Coprime (EffectiveZeroCycle.degree f w) 3 := hw.symm ▸ hi
  obtain ⟨x, _, hx⟩ := EffectiveZeroCycle.exists_coprime_degree f w hc
  obtain ⟨z₃, hz₃⟩ := hypersurface_fiber_exists_zeroCycle_degree_three 0 1 (by decide) p hp b
  exact ZeroCycle.exists_degree_one_of_coprime f z₃ hz₃ x hx

end AllCharacteristics

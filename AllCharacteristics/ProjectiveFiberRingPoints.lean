import AllCharacteristics.ProjectiveRingPoints
import AllCharacteristics.HomogeneousFiberPoints
import AllCharacteristics.ProperCyclePushforward

/-!
# Ring-valued points and cycles on actual projective fibers

A unit-coordinate solution over an algebra of the fiber's coefficient ring
produces a point of the actual pullback fiber. If that algebra is finite over
a field, its fundamental cycle pushes forward with the full algebra dimension.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
open HomogeneousProjective
universe u

/-- A unit-coordinate solution of the mapped equation over a ring gives a
point of the actual pullback fiber, with its specified structure morphism. -/
theorem hypersurface_fiber_point_of_unit_coordinates
    {R k A : Type u} [CommRing R] [CommRing k] [CommRing A] {σ : Type}
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (b : R →+* k) (f : k →+* A) (x : σ → A) (j : σ) (hx : IsUnit (x j))
    (he : (p.map b).eval₂ f x = 0) :
    ∃ q : Spec (.of A) ⟶
        pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)),
      q ≫ pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) =
        Spec.map (CommRingCat.ofHom f) := by
  have he' : p.eval₂ (f.comp b) x = 0 := by
    simpa only [MvPolynomial.eval₂_map] using he
  obtain ⟨q, hq⟩ := hypersurface_point_of_unit_coordinates (f.comp b) p hp x j hx he'
  refine ⟨pullback.lift q (Spec.map (CommRingCat.ofHom f)) ?_, pullback.lift_snd _ _ _⟩
  rw [hq, ← Spec.map_comp]
  rfl

/-- A solution over a finite algebra, with a unit coordinate, supplies an
actual effective cycle on the hypersurface fiber of exactly the algebra's
vector-space dimension. -/
theorem hypersurface_fiber_cycle_of_finite_algebra_solution
    {R k A : Type u} [CommRing R] [Field k] [CommRing A] [Algebra k A]
    [Module.Finite k A] {σ : Type} [Finite σ]
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (b : R →+* k)
    (x : σ → A) (j : σ) (hx : IsUnit (x j))
    (he : (p.map b).eval₂ (algebraMap k A) x = 0) :
    ∃ z : EffectiveZeroCycle
        (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))),
      EffectiveZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z =
        Module.finrank k A := by
  obtain ⟨q, hq⟩ := hypersurface_fiber_point_of_unit_coordinates p hp b
    (algebraMap k A) x j hx he
  exact exists_effectiveZeroCycle_of_finite_algebra_point
    (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) q hq

end AllCharacteristics

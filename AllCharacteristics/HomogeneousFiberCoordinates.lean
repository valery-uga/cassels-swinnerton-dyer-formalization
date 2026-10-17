import AllCharacteristics.HomogeneousFiberPoints
import AllCharacteristics.ClosedPointAlgebra

/-!
# Residue-field coordinates on actual pullback fibers

The point-to-base morphism of an actual fiber defines its residue-field algebra
over the fiber's field. Composing the residue point with the first projection
retains that algebra structure. For hypersurfaces this gives a nonzero solution
of the mapped polynomial over the same residue field, without requiring a
scheme-level Proj base-change isomorphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- A point of an actual fiber gives a point of the original scheme over the
composite map to its residue field, with the field algebra induced by the
fiber's structure morphism. -/
theorem fiber_residueField_pointOver
    {R k : Type u} [CommRing R] [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (b : R →+* k)
    (x : (pullback f (Spec.map (CommRingCat.ofHom b)) : Scheme.{u})) :
    letI := pointAlgebra (pullback.snd f (Spec.map (CommRingCat.ofHom b))) x
    HasPointOver f ((algebraMap k
      ((pullback f (Spec.map (CommRingCat.ofHom b))).residueField x)).comp b) := by
  let B := Spec.map (CommRingCat.ofHom b)
  let Y := pullback f B
  let g := pullback.snd f B
  let := pointAlgebra g x
  refine ⟨Y.fromSpecResidueField x ≫ pullback.fst f B, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    ← pointAlgebra_spec g x, ← Spec.map_comp]
  rfl

/-- Points of an actual hypersurface fiber supply nonzero solutions of the
mapped equation over their actual residue fields, with the correct base-field
algebras. Inseparable closed points are included. -/
theorem hypersurface_fiber_residueField_coordinates
    {R k : Type u} [CommRing R] [Field k] {σ : Type}
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (b : R →+* k)
    (x : (pullback (HomogeneousProjective.hypersurfaceToBase p hp)
      (Spec.map (CommRingCat.ofHom b)) : Scheme.{u})) :
    letI := pointAlgebra
      (pullback.snd (HomogeneousProjective.hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom b))) x
    ∃ v : σ → (pullback (HomogeneousProjective.hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom b))).residueField x,
      v ≠ 0 ∧ (p.map b).eval₂ (algebraMap k
        ((pullback (HomogeneousProjective.hypersurfaceToBase p hp)
          (Spec.map (CommRingCat.ofHom b))).residueField x)) v = 0 := by
  let f := HomogeneousProjective.hypersurfaceToBase p hp
  let B := Spec.map (CommRingCat.ofHom b)
  let Y := pullback f B
  let g := pullback.snd f B
  let := pointAlgebra g x
  obtain ⟨q, hq⟩ := fiber_residueField_pointOver f b x
  obtain ⟨v, hv, he⟩ := HomogeneousProjective.hypersurface_coordinates_of_point
    ((algebraMap k (Y.residueField x)).comp b) p hp q hq
  exact ⟨v, hv, by simpa only [MvPolynomial.eval₂_map] using he⟩

end AllCharacteristics

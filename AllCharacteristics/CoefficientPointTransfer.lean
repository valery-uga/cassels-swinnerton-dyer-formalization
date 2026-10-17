import AllCharacteristics.HomogeneousClosedPoints

/-!
# Points across coefficient reduction

Field-valued points of a coefficient-changed equation yield points of the
original projective family over the composite coefficient map. For a closed
point of the changed hypersurface this uses its actual residue field and the
algebra structure induced by its scheme morphism.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace HomogeneousProjective
universe u

/-- A field-valued point of a changed equation gives a point of the original
projective family over the composite coefficient map. -/
theorem hasPointOver_of_coefficient_map_eq
    {R k L : Type u} [CommRing R] [CommRing k] [Field L] {σ : Type}
    (b : R →+* k) (g : k →+* L)
    (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (hmap : q.map b = p)
    (h : HasPointOver (hypersurfaceToBase p hp) g) :
    HasPointOver (hypersurfaceToBase q hq) (g.comp b) := by
  obtain ⟨v, hv, he⟩ := (hypersurface_has_point_iff_coordinates g p hp).mp h
  apply (hypersurface_has_point_iff_coordinates (g.comp b) q hq).mpr
  refine ⟨v, hv, ?_⟩
  rw [← MvPolynomial.eval₂_map, hmap]
  exact he

/-- A point of the reduced hypersurface gives a point of the original family
over its same residue field, with the actual base-field algebra unchanged. -/
theorem pointOver_of_reduced_point
    {R k : Type u} [CommRing R] [Field k] {σ : Type}
    (b : R →+* k) (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (hmap : q.map b = p)
    (x : hypersurface p hp) :
    letI := pointAlgebra (hypersurfaceToBase p hp) x
    HasPointOver (hypersurfaceToBase q hq)
      ((algebraMap k ((hypersurface p hp).residueField x)).comp b) := by
  let := pointAlgebra (hypersurfaceToBase p hp) x
  apply hasPointOver_of_coefficient_map_eq b
    (algebraMap k ((hypersurface p hp).residueField x)) q hq p hp hmap
  exact ⟨(hypersurface p hp).fromSpecResidueField x,
    (pointAlgebra_spec (hypersurfaceToBase p hp) x).symm⟩

end HomogeneousProjective
end AllCharacteristics

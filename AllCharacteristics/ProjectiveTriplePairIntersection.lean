import AllCharacteristics.ProjectiveTripleOverlap

/-!
# Triple intersections as pullbacks of pair intersections

The actual triple-product spectrum is the intersection of the first and outer
pair overlaps over their common first coordinate chart.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- The first and outer pair restrictions form the actual triple intersection
over their shared first affine chart. -/
theorem isPullback_chartTripleFirstOuter (i j l : σ) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartTripleFromFirstPair I i j l)))
      (Spec.map (CommRingCat.ofHom (chartTripleFromOuterPair I i j l)))
      (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I i j)))
      (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I i l))) := by
  apply IsPullback.of_bot _ _ (isPullback_chartOverlap I i l)
  · rw [chartOverlapLeftMap_toProj, ← specMap_ringHom_comp, ← chartTriple_last_compat]
    exact isPullback_chartTripleOverlap I i j l
  · rw [← specMap_ringHom_comp, ← specMap_ringHom_comp, chartTriple_first_compat]

end HomogeneousProjective
end AllCharacteristics

import AllCharacteristics.CubicFiberDescent
import AllCharacteristics.HomogeneousRegularSpecialization

/-!
# Specializing cubic points from finite flat closed subschemes

An actual finite flat finitely presented closed subscheme of a projective cubic
family supplies a generic effective cycle with the same degree as its closed
fiber rank. If that rank is four or five and the fraction field has
characteristic zero, descent and proper specialization give a nonzero solution
of the reduced cubic in arbitrary characteristic. The finite flat subscheme is
an explicit geometric input; its construction from a special-fiber point is
still required.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open HomogeneousProjective
universe u

/-- A finite flat closed subscheme of rank four or five in a cubic family over
a regular local ring gives a point of the reduced cubic whenever the fraction
field has characteristic zero. The subscheme and its morphisms are actual
schemes, and nonreduced or inseparable special fibers are allowed. -/
theorem specialize_cubic_finite_flat_subscheme_rank_four_or_five
    {R K : Type u} [CommRing R] [IsRegularLocalRing R]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] [Flat (i ≫ hypersurfaceToBase p hp)]
    [LocallyOfFinitePresentation (i ≫ hypersurfaceToBase p hp)]
    (hi : (i ≫ hypersurfaceToBase p hp).finrank (IsLocalRing.closedPoint R) = 4 ∨
      (i ≫ hypersurfaceToBase p hp).finrank (IsLocalRing.closedPoint R) = 5) :
    ∃ y : Fin 4 → IsLocalRing.ResidueField R, y ≠ 0 ∧
      p.eval₂ (IsLocalRing.residue R) y = 0 := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_ambient_fiber i (hypersurfaceToBase p hp)
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have hd := hi.imp (hz.trans ·) (hz.trans ·)
  obtain ⟨x, hx, he⟩ := hypersurface_fiber_coordinates_of_effective_degree_four_or_five
    p hp (algebraMap R K) z hd
  exact specialize_homogeneous_equation_regularLocal p hp x hx he

end AllCharacteristics

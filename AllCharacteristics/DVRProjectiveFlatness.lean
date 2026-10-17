import AllCharacteristics.DVRPolynomialFlatness
import AllCharacteristics.HomogeneousChartFlatness
import AllCharacteristics.CoordinateCharts
import AllCharacteristics.SmoothSpecialFiber

/-!
# Flatness of projective hypersurfaces over a DVR

The flat polynomial quotient gives flat coordinate charts of the actual Proj.
They cover the projective scheme, so its structure morphism is flat. Properness
and finite presentation then turn smoothness of the closed fiber into
smoothness of the entire lifted hypersurface.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Flatness of the homogeneous coordinate algebra over a Dedekind domain
implies flatness of the actual projective structure morphism. -/
theorem flat_toBase_of_flat_coordinateRing
    {R : Type u} {σ : Type} [CommRing R] [IsDedekindDomain R]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    [Module.Flat R (CoordinateRing I)] : Flat (toBase I) := by
  have : IsZariskiLocalAtSource (@AlgebraicGeometry.Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat.{u})
    (coordinateOpenCover I).openCover).mpr
  intro j
  change σ at j
  change Flat (chartι I j ≫ toBase I)
  rw [chartι_toBase]
  apply Flat.SpecMap_iff.mpr
  exact homogeneousAway_flat_of_flat (grading I) (coordinate I j)

/-- A projective homogeneous hypersurface with nonzero residue equation is
flat over its discrete valuation coefficient ring. -/
theorem flat_hypersurfaceToBase_of_nonzero_reduction
    {R : Type u} {σ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (hred : p.map (residue R) ≠ 0) : Flat (hypersurfaceToBase p hp) := by
  have : Module.Flat R (CoordinateRing (equationIdeal p hp)) :=
    polynomial_quotient_flat_of_nonzero_reduction p hred
  exact flat_toBase_of_flat_coordinateRing (equationIdeal p hp)

/-- A projective hypersurface over a DVR with nonzero residue equation and
smooth closed fiber is smooth over the entire coefficient ring. -/
theorem smooth_hypersurfaceToBase_of_smooth_closed_fiber
    {R : Type u} {σ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite σ] (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (hred : p.map (residue R) ≠ 0)
    (hsm : Smooth ((hypersurfaceToBase p hp).fiberToSpecResidueField (closedPoint R))) :
    Smooth (hypersurfaceToBase p hp) := by
  have := flat_hypersurfaceToBase_of_nonzero_reduction p hp hred
  exact smooth_of_smooth_closed_fiber (hypersurfaceToBase p hp) hsm

end HomogeneousProjective
end AllCharacteristics

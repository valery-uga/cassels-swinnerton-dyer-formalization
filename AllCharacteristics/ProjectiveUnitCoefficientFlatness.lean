import AllCharacteristics.ProjectiveChartRetraction
import AllCharacteristics.UnitCoefficientFlatness
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat projective hypersurfaces on coefficient opens

Flatness of a homogeneous polynomial quotient passes to its actual Proj
through the coordinate-chart retractions. A homogeneous equation with a unit
coefficient therefore defines a flat projective family over any coefficient
ring. Inverting any coefficient supplies such a family on that base open.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace HomogeneousProjective
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A flat homogeneous coordinate algebra gives a flat actual projective
scheme over an arbitrary commutative coefficient ring. -/
theorem flat_toBase_of_flat_homogeneous_quotient
    {R : Type u} {σ : Type} [CommRing R]
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
  exact flat_chartRing_of_flat_coordinateRing I j

/-- A unit coefficient makes a homogeneous equation's projective family
flat over its coefficient ring, in every characteristic. -/
theorem flat_hypersurfaceToBase_of_isUnit_coeff
    {R : Type u} {σ : Type} [CommRing R] [Finite σ]
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : σ →₀ ℕ) (hm : IsUnit (p.coeff m)) : Flat (hypersurfaceToBase p hp) := by
  have : Module.Flat R (CoordinateRing (equationIdeal p hp)) :=
    mvPolynomial_quotient_flat_of_isUnit_coeff p m hm
  exact flat_toBase_of_flat_homogeneous_quotient (equationIdeal p hp)

/-- Inverting any coefficient of a homogeneous equation yields a flat actual
projective hypersurface over the localized coefficient ring. -/
theorem flat_hypersurfaceToBase_after_localizing_coeff
    {R : Type u} {σ : Type} [CommRing R] [Finite σ]
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : σ →₀ ℕ) (S : Type v) [CommRing S] [Algebra R S]
    [IsLocalization.Away (p.coeff m) S] :
    Flat (hypersurfaceToBase (p.map (algebraMap R S)) (hp.map (algebraMap R S))) := by
  apply flat_hypersurfaceToBase_of_isUnit_coeff _ _ m
  rw [MvPolynomial.coeff_map]
  exact IsLocalization.map_units S ⟨p.coeff m, Submonoid.mem_powers _⟩

end HomogeneousProjective
end AllCharacteristics

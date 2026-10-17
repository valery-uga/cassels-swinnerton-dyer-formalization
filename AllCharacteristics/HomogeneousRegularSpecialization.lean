import AllCharacteristics.ProjectivePoints
import AllCharacteristics.RegularLocalSpecialization

/-!
# Homogeneous equations specialize over regular local rings

The coordinate/scheme comparison turns proper specialization into an explicit
nonzero solution of the reduced equations. The regular local ring can have any
dimension and any residue characteristic.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {R K : Type u} [CommRing R] [IsRegularLocalRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero common solution of a homogeneous ideal over the fraction field
specializes to a nonzero common solution over the residue field of an arbitrary
regular local ring. -/
theorem specialize_homogeneous_ideal_regularLocal
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (x : σ → K) (hx : x ≠ 0)
    (he : ∀ p : MvPolynomial σ R, p ∈ I.toIdeal → p.eval₂ (algebraMap R K) x = 0) :
    ∃ y : σ → IsLocalRing.ResidueField R, y ≠ 0 ∧
      ∀ p : MvPolynomial σ R, p ∈ I.toIdeal → p.eval₂ (IsLocalRing.residue R) y = 0 := by
  have hgeneric : HasPointOver (HomogeneousProjective.toBase I) (algebraMap R K) :=
    HomogeneousProjective.point_of_coordinates I (algebraMap R K) x hx he
  obtain ⟨q, hq⟩ := specialize_proper_point_regularLocal (HomogeneousProjective.toBase I) hgeneric
  exact HomogeneousProjective.homogeneous_coordinates_of_point I (IsLocalRing.residue R) q hq

/-- A homogeneous hypersurface solution over the fraction field specializes to
a nonzero solution of the reduced equation over the residue field, in arbitrary
dimension and characteristic. -/
theorem specialize_homogeneous_equation_regularLocal (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) (x : σ → K) (hx : x ≠ 0)
    (he : p.eval₂ (algebraMap R K) x = 0) :
    ∃ y : σ → IsLocalRing.ResidueField R, y ≠ 0 ∧
      p.eval₂ (IsLocalRing.residue R) y = 0 := by
  have hgeneric : HasPointOver (HomogeneousProjective.hypersurfaceToBase p hp)
      (algebraMap R K) :=
    HomogeneousProjective.hypersurface_point_of_coordinates (algebraMap R K) p hp x hx he
  obtain ⟨q, hq⟩ := specialize_proper_point_regularLocal
    (HomogeneousProjective.hypersurfaceToBase p hp) hgeneric
  exact HomogeneousProjective.hypersurface_coordinates_of_point (IsLocalRing.residue R) p hp q hq

end AllCharacteristics

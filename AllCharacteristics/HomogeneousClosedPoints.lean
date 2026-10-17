import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.ProjectivePoints

/-!
# Coordinates over the residue fields of projective points

A point of a homogeneous projective scheme provides a nonzero solution over
its actual residue field with the algebra structure induced by the structure
morphism. For closed points with finitely many projective coordinates, the
extension is finite and retains its full residue degree.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {k : Type u} [Field k] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every scheme point supplies homogeneous coordinates over its own residue
field, with the base algebra induced by the actual structure morphism. -/
theorem residueField_coordinates
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k)) (x : scheme I) :
    letI := pointAlgebra (toBase I) x
    ∃ v : σ → (scheme I).residueField x, v ≠ 0 ∧
      ∀ p : MvPolynomial σ k, p ∈ I.toIdeal →
        p.eval₂ (algebraMap k ((scheme I).residueField x)) v = 0 := by
  let := pointAlgebra (toBase I) x
  exact homogeneous_coordinates_of_point I
    (algebraMap k ((scheme I).residueField x)) ((scheme I).fromSpecResidueField x)
    (pointAlgebra_spec (toBase I) x).symm

/-- Every point of a projective hypersurface is a nonzero solution over its
actual residue field, compatibly with the base field. -/
theorem hypersurface_residueField_coordinates
    (p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d) (x : hypersurface p hp) :
    letI := pointAlgebra (hypersurfaceToBase p hp) x
    ∃ v : σ → (hypersurface p hp).residueField x, v ≠ 0 ∧
      p.eval₂ (algebraMap k ((hypersurface p hp).residueField x)) v = 0 := by
  let := pointAlgebra (hypersurfaceToBase p hp) x
  exact hypersurface_coordinates_of_point
    (algebraMap k ((hypersurface p hp).residueField x)) p hp
    ((hypersurface p hp).fromSpecResidueField x)
    (pointAlgebra_spec (hypersurfaceToBase p hp) x).symm

end HomogeneousProjective
end AllCharacteristics

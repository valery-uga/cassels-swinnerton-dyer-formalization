import PfaffianDescent.ProjectiveFiniteChartArtinian
import PfaffianDescent.TripleCompleteIntersectionJacobian

/-!
# Artinian coordinate presentations of finite three-quadric intersections

For a finite projective three-quadric intersection, every normalized
coordinate presentation is an Artinian quotient by the three quadrics and
the equation setting its distinguished coordinate to one.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

section

variable {K : Type u} [Field K] {a b c : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The concrete affine chart quotient by three homogeneous equations and
`X_j - 1` is Artinian when their projective intersection is finite. -/
theorem tripleCompleteIntersection_chartRelations_isArtinian_of_finite
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (j : Fin 4) :
    IsArtinianRing (MvPolynomial (Fin 4) K ⧸
      Ideal.span (Set.range (tripleCompleteIntersectionChartRelations p q r j))) := by
  letI : Algebra K
      (ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) :=
    (chartBaseMap (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j).toAlgebra
  letI : IsArtinianRing
      (ChartRing (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) :=
    projective_chart_isArtinian_of_finite
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j
  exact (tripleCompleteIntersectionChartRelationsEquiv p q r hp hq hr j).symm.isArtinianRing

end

end PfaffianDescent

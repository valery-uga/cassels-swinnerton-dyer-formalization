import PfaffianDescent.DehomogenizedQuadricsRelativePrime
import PfaffianDescent.TripleQuadricsDehomogenizedArtinian

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- On each normalized projective chart, the third equation of a finite
three-quadric intersection is regular modulo the first two. -/
theorem tripleCompleteIntersection_coordinateOne_third_regular_of_finite_algClosed
    (p q r : MvPolynomial (Fin 4) K) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (hapos : 0 < a)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (j : Fin 4) (a : MvPolynomial {i : Fin 4 // i ≠ j} K)
    (ha : coordinateOneEvaluation j r * a ∈ Ideal.span
      ({coordinateOneEvaluation j p, coordinateOneEvaluation j q} :
        Set (MvPolynomial {i : Fin 4 // i ≠ j} K))) :
    a ∈ Ideal.span ({coordinateOneEvaluation j p, coordinateOneEvaluation j q} :
      Set (MvPolynomial {i : Fin 4 // i ≠ j} K)) := by
  letI : IsArtinianRing (MvPolynomial {i : Fin 4 // i ≠ j} K ⧸
      Ideal.span ({coordinateOneEvaluation j p, coordinateOneEvaluation j q,
        coordinateOneEvaluation j r} : Set (MvPolynomial {i : Fin 4 // i ≠ j} K))) := by
    change IsArtinianRing (MvPolynomial {i : Fin 4 // i ≠ j} K ⧸
      tripleCompleteIntersectionDehomogenizedIdeal p q r j)
    exact tripleCompleteIntersection_dehomogenized_isArtinian_of_finite p q r hp hq hr j
  apply third_regular_of_pair_relPrime_of_artinian_algClosed
    (finThreeEquivCoordinateComplement j)
    (coordinateOneEvaluation j p) (coordinateOneEvaluation j q)
    (coordinateOneEvaluation j r)
  · exact coordinateOneEvaluation_ne_zero_of_homogeneous hp hp0 j
  · exact QuarticNet.coordinateOneEvaluation_isRelPrime_of_homogeneous_isRelPrime
      hp hq hapos hp0 hrel j
  · exact ha

end PfaffianDescent

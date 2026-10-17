import PfaffianDescent.ProjectiveLinearCoordinateSchemeIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPositiveGradedPullbackIso

/-! SOURCE ONLY. Genuine degree-preserving native positive-twist pullback
along the inverse of the SAME original linear-coordinate scheme Iso. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native positive twists under the SAME original inverse coordinate Iso.
No coefficient/sheaf identification or desired degree premise is supplied. -/
def projectiveLinearCoordinatePositiveTwistInvIso
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom)
    (m : ℕ) :
    (Scheme.Modules.pullback (linearCoordinateChangeSchemeIso M hM I J hIJ).inv).obj
      (positiveSheafOfModules (grading I) m) ≅ positiveSheafOfModules (grading J) m := by
  let f := linearCoordinateChangeGradedHom M hM I J hIJ
  have hsurj : Function.Surjective f :=
    (Ideal.quotientEquivAlg I.toIdeal J.toIdeal (linearSubstitutionEquiv M hM) hIJ).surjective
  let hf := gradedSurjective_irrelevant_le f hsurj
  have hI : (HomogeneousIdeal.irrelevant (grading I)).toIdeal ≤
      Ideal.span (Set.range (fun q : grading I 1 => (q : CoordinateRing I))) :=
    gradedSurjective_irrelevant_le_span_degreeOne (homogeneousSubmodule (Fin 4) K) (grading I)
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  have hJ : (HomogeneousIdeal.irrelevant (grading J)).toIdeal ≤
      Ideal.span (Set.range (fun q : grading J 1 => (q : CoordinateRing J))) :=
    gradedSurjective_irrelevant_le_span_degreeOne (homogeneousSubmodule (Fin 4) K) (grading J)
      (quotientGradedRingHom J) (quotientGradedRingHom_surjective J)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  change (Scheme.Modules.pullback (Proj.map f hf)).obj
    (positiveSheafOfModules (grading I) m) ≅ positiveSheafOfModules (grading J) m
  exact cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackIso
    (grading I) (grading J) f hf hI hJ m

end PfaffianDescent

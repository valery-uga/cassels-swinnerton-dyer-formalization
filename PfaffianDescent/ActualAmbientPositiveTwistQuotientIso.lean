import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPositiveGradedPullbackIso
import AllCharacteristics.HomogeneousProjectiveAmbient

/- SOURCE ONLY / UNVERIFIED. Actual raw ambient O(m) pulls to the actual
quotient O(m) by its genuine graded restriction adjunct. All degree-one
generation hypotheses are derived, not geometric identification inputs. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualAmbientPositiveTwistQuotientIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) (m : ℕ) :
    (Scheme.Modules.pullback (quotientProjMap I)).obj
      (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) m) ≅
        positiveSheafOfModules (grading I) m :=
  cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackIso
    (MvPolynomial.homogeneousSubmodule (Fin 4) K) (grading I)
    (quotientGradedRingHom I) (irrelevant_le_map_quotientGradedRingHom I)
    mvPolynomial_irrelevant_le_span_degreeOne_small
    (gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) (grading I)
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small) m

@[simp] lemma actualAmbientPositiveTwistQuotientIso_hom
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) (m : ℕ) :
    (actualAmbientPositiveTwistQuotientIso I m).hom =
      cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) (grading I)
        (quotientGradedRingHom I) (irrelevant_le_map_quotientGradedRingHom I) m := rfl

end PfaffianDescent

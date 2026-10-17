import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPositiveGradedPullbackIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoefficientIdealIso
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K L : Type u} [Field K] [Field L] (g : K →+* L)
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
/-- Every actual native positive twist pulls back to the actual native twist
of the coefficient-extended cubic, with no identification hypothesis. -/
def cubicClosedPointSerreFiniteZeroResidual_coefficientPositiveTwistIso (m : ℕ) :
    (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap g p hp)).obj
        (positiveSheafOfModules (grading (equationIdeal p hp)) m) ≅
      positiveSheafOfModules (grading (equationIdeal (p.map g) (hp.map g))) m := by
  let I := equationIdeal p hp
  let J := equationIdeal (p.map g) (hp.map g)
  exact cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackIso
    (grading I) (grading J) (gradedCoefficientMap g I J (equationIdeal_map g p hp))
    (irrelevant_le_map_gradedCoefficientMap g I J (equationIdeal_map g p hp))
    (gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) (grading I)
      (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)
      mvPolynomial_irrelevant_le_span_degreeOne_small)
    (gradedSurjective_irrelevant_le_span_degreeOne
      (MvPolynomial.homogeneousSubmodule (Fin 4) L) (grading J)
      (quotientGradedRingHom J) (quotientGradedRingHom_surjective J)
      mvPolynomial_irrelevant_le_span_degreeOne_small) m


end PfaffianDescent.ProjectiveNegativeTwist

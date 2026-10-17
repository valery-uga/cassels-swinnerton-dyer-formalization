import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentLinearChartResidue
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentTensor

noncomputable section
open AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual common-chart K-algebra map, with its literal coefficient
map retained for the native cotangent and point-pullback adapters. -/
def cubicClosedPointSerreSurfaceJetCotangent_linearChartJetAlgHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (J : Fin 4 → CubicSurfaceFirstJet K)
    (hunit : IsUnit (aeval J ell)) (hzero : aeval J p = 0) :
    letI := (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal p hp))
      (z := Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)).toAlgebra
    Away (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) →ₐ[K] CubicSurfaceFirstJet K := by
  letI := (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal p hp))
    (z := Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)).toAlgebra
  exact { cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap
      p hp ell hell J hunit hzero with
    commutes' := fun r => linearNormalizedPointChartMap_base (equationIdeal p hp)
      (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit) ell
      (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ell ell J hell hunit)
      (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ideal_zero p hp ell J hunit hzero) r }

end PfaffianDescent

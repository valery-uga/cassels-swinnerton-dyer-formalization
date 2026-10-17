import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentGradedFractionLinear
import PfaffianDescent.CubicHomogeneousChartRestriction
import PfaffianDescent.CubicElevenPointGroundRestrictionSurjective

noncomputable section
open MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Native polynomial interpolation descends to the actual degree-three
surface coordinate piece, with the literal chart fraction restriction. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_gradedRestriction_surjective_of_kernel_nine
    {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap K L)
    (hL : Module.finrank K L = 11)
    (hker : Module.finrank K (cubicHomogeneousChartRestriction I ell ell.2 g).ker = 9) :
    Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_gradedFractionRestriction (grading I) ell g hbase) := by
  have honto := cubicElevenPoint_groundRestriction_surjective
    (cubicHomogeneousChartRestriction I ell ell.2 g) hL hker
  intro x
  obtain ⟨q, hq⟩ := honto x
  refine ⟨⟨(quotientGradedRingHom I) q,
    (quotientGradedRingHom I).map_mem q.2⟩, ?_⟩
  exact (cubicHomogeneousChartRestriction_fraction I ell ell.2 g hbase q).trans hq

end PfaffianDescent

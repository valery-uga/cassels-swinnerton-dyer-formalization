import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelConverse
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentGradedFractionLinear
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentExactKernelLinearEquiv
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveGlobalLinearApply

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Actual global ideal sections equal the literal graded chart fraction
kernel. The chart ideal and the actual global ideal are preserved throughout. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveIdealGlobalKernelEquiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap K L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (e : grading I 3 ≃ₗ[K] SchemeModuleGlobalSectionsOver (toBase I)
      (positiveSheafOfModules (grading I) 3))
    (he : ∀ q, e q = (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading I) 3 q)) :
    SchemeModuleGlobalSectionsOver (toBase I)
      (closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
        (positiveSheafOfModules (grading I) 3)) ≃ₗ[K]
      (cubicClosedPointSerreSurfaceJetCotangent_gradedFractionRestriction (grading I) ell g hbase).ker := by
  let i := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
  let T := positiveSheafOfModules (grading I) 3
  let S := closedImmersionIdealTwistSequence i T
  let a := cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I i
  let R := cubicClosedPointSerreSurfaceJetCotangent_gradedFractionRestriction (grading I) ell g hbase
  let A := e.symm.toLinearMap.comp (schemeModuleGlobalSectionsMap (toBase I) a)
  letI : PreservesFiniteLimits (schemeModuleTensorRight T) :=
    quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
  have hS := quotientPositiveTwist_closedImmersionIdealTwistSequence_shortExact I i 3
  letI : Mono S.f := hS.mono_f
  letI : Mono a := inferInstanceAs (Mono (S.f ≫ (schemeModuleTensorUnitLeftIso T).hom))
  have ha : Function.Injective A := by
    intro s t h
    apply (cancel_mono a).mp
    exact e.symm.injective h
  have hz : ∀ v, R (A v) = 0 := by
    intro v
    have hv : v ≫ a = e (A v) := (e.apply_symm_apply (v ≫ a)).symm
    have hq := cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_fraction_zero_of_lift
      I ell g (A v) v (hv.trans (he (A v)))
    exact hq
  have hlift : ∀ q, R q = 0 → ∃ v, A v = q := by
    intro q hq
    obtain ⟨v, hv, _⟩ :=
      cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_globalLift I ell g q hq
    refine ⟨v, ?_⟩
    change e.symm (v ≫ a) = q
    rw [hv, ← he q, e.symm_apply_apply]
  exact cubicClosedPointSerreSurfaceJetCotangent_exactKernelLinearEquiv A R ha hz hlift

end PfaffianDescent

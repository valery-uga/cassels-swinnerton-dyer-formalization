import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveGlobalLinearApply
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveLinearSectionCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentGradedRestrictionSurjective

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual global O(3) restriction in the native positive chart coordinate. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveGlobalChartRestriction
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap K L)
    (e : grading I 3 ≃ₗ[K] SchemeModuleGlobalSectionsOver (toBase I)
      (positiveSheafOfModules (grading I) 3)) :
    SchemeModuleGlobalSectionsOver (toBase I)
      (positiveSheafOfModules (grading I) 3) →ₗ[K] L :=
  (cubicClosedPointSerreSurfaceJetCotangent_gradedFractionRestriction
    (grading I) ell g hbase).comp e.symm.toLinearMap

/-- This linear restriction is literally actual module restriction followed
by the native positive-three unit coordinate and the actual chart point g. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveGlobalChartRestriction_coordinate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap K L)
    (e : grading I 3 ≃ₗ[K] SchemeModuleGlobalSectionsOver (toBase I)
      (positiveSheafOfModules (grading I) 3))
    (he : ∀ q, e q = (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading I) 3 q))
    (s : SchemeModuleGlobalSectionsOver (toBase I) (positiveSheafOfModules (grading I) 3)) :
    cubicClosedPointSerreSurfaceJetCotangent_positiveGlobalChartRestriction I ell g hbase e s =
      g ((affineGlobalSectionsUnitLinearEquiv (A := Away (grading I) (ell : CoordinateRing I)))
        (unitEndomorphismValue ((Scheme.Modules.restrictUnitIso
          (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).inv ≫
          (Scheme.Modules.restrictFunctor
            (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).map s ≫
          (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeLinearChartUnitIso I ell).hom))) := by
  obtain ⟨q, rfl⟩ := e.surjective s
  change (cubicClosedPointSerreSurfaceJetCotangent_gradedFractionRestriction
    (grading I) ell g hbase) (e.symm (e q)) = _
  rw [e.symm_apply_apply]
  change g (Away.mk (grading I) ell.2 3 (q : CoordinateRing I) _) = _
  rw [he q, cubicClosedPointSerreSurfaceJetCotangent_positiveLinearSectionCoefficient,
    LinearEquiv.apply_symm_apply]

/-- Native interpolation in the polynomial kernel gives actual global O(3)
restriction onto the degree-eleven field. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveGlobalChartRestriction_surjective
    {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap K L)
    (e : grading I 3 ≃ₗ[K] SchemeModuleGlobalSectionsOver (toBase I)
      (positiveSheafOfModules (grading I) 3))
    (hL : Module.finrank K L = 11)
    (hker : Module.finrank K (cubicHomogeneousChartRestriction I ell ell.2 g).ker = 9) :
    Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_positiveGlobalChartRestriction I ell g hbase e) :=
  (cubicClosedPointSerreSurfaceJetCotangent_gradedRestriction_surjective_of_kernel_nine
    I ell g hbase hL hker).comp e.symm.surjective

end PfaffianDescent

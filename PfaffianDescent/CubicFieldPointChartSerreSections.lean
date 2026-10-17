import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealGlobalDimension
import PfaffianDescent.CubicClosedPointSerreExactSectionDimension
import PfaffianDescent.CubicFieldPointChartClosedImmersion
import PfaffianDescent.CubicClosedPointSerreLocalFreeExistence

/-! Exact global Serre-section dimension from actual chart interpolation.
The eight-dimensional ideal-section space is proved internally. -/

noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldPointChartSerreSections_finrank_nine
    {F L : Type u} [Field F] [Infinite F] [Field L] [Algebra F L]
    [FiniteDimensional F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) F)).Modules]
    [HasExt.{u} (hypersurface P hP).Modules]
    (ell : grading (equationIdeal P hP) 1)
    (g : Away (grading (equationIdeal P hP)) (ell : CoordinateRing (equationIdeal P hP)) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal P hP))
      (z := (ell : CoordinateRing (equationIdeal P hP)))) = algebraMap F L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ell g)]
    (hL : Module.finrank F L = 11)
    (hker : Module.finrank F
      (cubicHomogeneousChartRestriction (equationIdeal P hP) ell ell.2 g).ker = 9)
    (e : SerreExtensionSequenceData (hypersurface P hP)
      (closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
          (equationIdeal P hP) ell g)
        (positiveSheafOfModules (grading (equationIdeal P hP)) 3))) :
    Module.finrank F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
      (show (hypersurface P hP).Modules from e.E)) = 9 := by
  have hQ := cubicClosedPointSerreSurfaceJetCotangent_positiveIdealGlobal_finrank_eight
    P hP hP0 ell g hbase hL hker
  exact cubicClosedPointSerreSection_finrank_eq_nine_of_ideal_finrank F P hP hP0
    (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ell g) hQ e

end PfaffianDescent.ProjectiveNegativeTwist

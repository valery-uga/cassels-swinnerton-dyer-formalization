import PfaffianDescent.VoisinCubicThreeGlobalSections
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealGlobalKernel
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentGradedRestrictionSurjective

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The ACTUAL positive-three ideal has eight global sections. Smoothness
supplies the nineteen-dimensional global cubic model; the actual native
polynomial kernel nine supplies restriction onto the degree-eleven point. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveIdealGlobal_finrank_eight
    {K L : Type u} [Field K] [Infinite K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    (ell : grading (equationIdeal p hp) 1)
    (g : Away (grading (equationIdeal p hp)) (ell : CoordinateRing (equationIdeal p hp)) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal p hp))
      (z := (ell : CoordinateRing (equationIdeal p hp)))) = algebraMap K L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal p hp) ell g)]
    (hL : Module.finrank K L = 11)
    (hker : Module.finrank K
      (cubicHomogeneousChartRestriction (equationIdeal p hp) ell ell.2 g).ker = 9) :
    Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion (equationIdeal p hp) ell g)
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3))) = 8 := by
  let I := equationIdeal p hp
  let e := cubicPositiveThreeGlobalSectionsLinearEquiv K p hp hp0
  let eI := cubicClosedPointSerreSurfaceJetCotangent_positiveIdealGlobalKernelEquiv I ell g hbase e
    (fun q => cubicClosedPointSerreSurfaceJetCotangent_positiveGlobalLinearApply I q)
  erw [eI.finrank_eq]
  let R := cubicClosedPointSerreSurfaceJetCotangent_gradedFractionRestriction (grading I) ell g hbase
  change Module.finrank K R.ker = 8
  letI : Module.Finite K (grading I 3) := polynomialQuotientGrade_finite I 3
  have honto := cubicClosedPointSerreSurfaceJetCotangent_gradedRestriction_surjective_of_kernel_nine
    I ell g hbase hL hker
  have h := R.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr honto, finrank_top, hL,
    cubicSurface_grade_three_finrank p hp hp0] at h
  omega

end PfaffianDescent

import PfaffianDescent.CubicHomogeneousChartRestriction
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelWitness

/-! An actual homogeneous-polynomial restriction-kernel element supplies
the actual positive ideal global section and its actual point derivative.
The global-lift and fibre witnesses are constructed internally. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def cubicGroundKernelPolynomialClass
    {F : Type u} [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (q : homogeneousSubmodule (Fin 4) F 3) : grading I 3 :=
  ⟨(quotientGradedRingHom I) q, (quotientGradedRingHom I).map_mem q.2⟩

theorem cubicGroundKernelPolynomialClass_fraction_eq
    {F : Type u} [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (q : homogeneousSubmodule (Fin 4) F 3) :
    Away.mk (grading I) ell.2 3 (cubicGroundKernelPolynomialClass I q : CoordinateRing I)
      (cubicGroundKernelPolynomialClass I q).2 =
    q.1.eval₂ (AllCharacteristics.GradedChart.baseMap (grading I) (z := (ell : CoordinateRing I)))
      (linearChartCoordinate I ell ell.2) :=
  (eval₂_linearChartCoordinate_eq_fraction I ell ell.2 q.1 q.2).symm

theorem cubicGroundKernelPolynomialClass_fraction_zero
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap F L)
    (q : homogeneousSubmodule (Fin 4) F 3)
    (hq : cubicHomogeneousChartRestriction I ell ell.2 g q = 0) :
    g (Away.mk (grading I) ell.2 3
      (cubicGroundKernelPolynomialClass I q : CoordinateRing I)
      (cubicGroundKernelPolynomialClass I q).2) = 0 :=
  (cubicHomogeneousChartRestriction_fraction I ell ell.2 g hbase q).trans hq

abbrev cubicGroundKernelPolynomial_globalFiberWitness
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap F L)
    (q : homogeneousSubmodule (Fin 4) F 3)
    (hq : cubicHomogeneousChartRestriction I ell ell.2 g q = 0)
    {E : Type u} [Field E]
    (φ : Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E)
    (β : L →+* E)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g) :=
  cubicClosedPointSerreSurfaceJetCotangent_exists_positiveCubicKernel_globalFiberWitness
    I ell g (cubicGroundKernelPolynomialClass I q)
    (cubicGroundKernelPolynomialClass_fraction_zero I ell g hbase q hq) φ β hres

end PfaffianDescent

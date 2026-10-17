import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelFiber
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelFiberMap

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual E-linear derivative map on Gamma of the ACTUAL point
pullback of I(3) evaluates the actual global cubic ideal lift as phi(q/ell^3). -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernelPointFiberDerivative_apply
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B] (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (q : grading I 3)
    (hq : g (Away.mk (grading I) ell.2 3 (q : CoordinateRing I)
      (by simpa using q.2)) = 0)
    (v : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
      closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
        (positiveSheafOfModules (grading I) 3))
    (hv : v ≫ cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g) =
      (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) 3 q))

    {E : Type u} [Field E]
    (φ : Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E)
    (β : B →+* E)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g) :
    cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernelPointFiberDerivative I ell g φ β hres
      ((pullbackSection
        (Spec.map (CommRingCat.ofHom
          (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ)) ≫
          cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)
        (closedImmersionIdealTwist
          (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
          (positiveSheafOfModules (grading I) 3))
        (isIso_pullbackUnitComparison _)
        ((closedImmersionIdealTwist
          (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
          (positiveSheafOfModules (grading I) 3)).unitHomEquiv v)).val (Opposite.op ⊤)) =
    (φ (Away.mk (grading I) ell.2 3 (q : CoordinateRing I) (by simpa using q.2))).snd := by
  exact cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_pointDerivative I ell g q hq v hv φ β hres

end PfaffianDescent

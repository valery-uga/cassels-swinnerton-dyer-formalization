import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelLift


noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The affine ideal lift has the exact native positive cubic coefficient. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_localCoefficient
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B] (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (q : grading I 3)
    (hq : g (Away.mk (grading I) ell.2 3 (q : CoordinateRing I)
      (by simpa using q.2)) = 0) :
    cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom g
      ⟨Away.mk (grading I) ell.2 3 (q : CoordinateRing I) (by simpa using q.2), hq⟩ ≫
      closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g)) =
    (Scheme.Modules.restrictUnitIso
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).inv ≫
      (Scheme.Modules.restrictFunctor
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).map
        ((positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous (grading I) 3 q)) ≫
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeLinearChartUnitIso I ell).hom := by
  let h : RingHom.ker g := ⟨Away.mk (grading I) ell.2 3 (q : CoordinateRing I)
    (by simpa using q.2), hq⟩
  let s := (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm (positiveGlobalSectionOfHomogeneous (grading I) 3 q)
  let t := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom g h
  let b := (Scheme.Modules.restrictUnitIso
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).inv ≫
    (Scheme.Modules.restrictFunctor
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).map s ≫
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeLinearChartUnitIso I ell).hom
  have hb : b = unitEndomorphismOfRegularFunction
      ((affineGlobalSectionsUnitLinearEquiv
        (A := Away (grading I) (ell : CoordinateRing I))).symm h.1) :=
    (unitEndomorphismOfRegularFunction_value b).symm.trans
      (congrArg unitEndomorphismOfRegularFunction
        (cubicClosedPointSerreSurfaceJetCotangent_positiveLinearSectionCoefficient I ell q))
  exact (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom_toUnit g h).trans hb.symm

end PfaffianDescent

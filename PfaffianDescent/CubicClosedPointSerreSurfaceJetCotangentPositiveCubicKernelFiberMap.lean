import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelChart
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointChartSectionHom
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelRingDerivative

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Derivatives on ACTUAL Gamma of the actual positive-three ideal point
pullback, through the internally constructed SAME-ideal chart coordinates. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernelPointFiberDerivative
    {K E : Type u} [Field K] [Field E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B] (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (φ : Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E)
    (β : B →+* E)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g) :
    (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom
          (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ)) ≫
          cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).obj
        (closedImmersionIdealTwist
          (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
          (positiveSheafOfModules (grading I) 3))) →ₗ[E] (Fin 2 → E) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let e := Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 Nat.zero_lt_one
  let M := closedImmersionIdealTwist
    (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
    (positiveSheafOfModules (grading I) 3)
  let N := closedImmersionModule (Spec.map (CommRingCat.ofHom g))
  let c := cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso U e.inv
    (positiveSheafOfModules (grading I) 3)
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell)
    (Spec.map (CommRingCat.ofHom g))
  let r := Spec.map (CommRingCat.ofHom
    (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ))
  let d := cubicClosedPointSerreSurfaceJetCotangent_pointChartModuleIso
    (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell) r M N c
  exact (cubicClosedPointSerreSurfaceJetCotangent_ringNativeIdealFiberDerivative φ g β hres).comp
    (((moduleSpecΓFunctor (R := CommRingCat.of E)).mapIso d).toLinearEquiv.toLinearMap)

end PfaffianDescent

import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartCoefficientKernel
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelLift
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealLinearChartInclusion

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private theorem fractionZeroOfLift
    {X : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion f]
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    {M T : X.Modules} (a : M ⟶ T)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅
      closedImmersionModule (Spec.map (CommRingCat.ofHom g)))
    (p : (Scheme.Modules.restrictFunctor f).obj T ≅
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf)
    (he : e.hom ≫ closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g)) =
      (Scheme.Modules.restrictFunctor f).map a ≫ p.hom)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T) (x : A)
    (hx : unitEndomorphismValue ((Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctor f).map s ≫ p.hom) =
      (affineGlobalSectionsUnitLinearEquiv (A := A)).symm x)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ M) (hv : v ≫ a = s) : g x = 0 := by
  have h := cubicClosedPointSerreSurfaceJetCotangent_idealChartCoefficientKernel f g a e p he v
  rw [hv, hx, LinearEquiv.apply_symm_apply] at h
  exact h

/-- A cubic whose ACTUAL global section lifts to the actual ideal has literal
chart fraction in ker g. Together with globalLift this is a native iff. -/
abbrev cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_fraction_zero_of_lift
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B] (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (q : grading I 3) :=
  fractionZeroOfLift
    (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell) g
    (cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g))
    (cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso
      (Proj.basicOpen (grading I) (ell : CoordinateRing I))
      (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 Nat.zero_lt_one).inv
      (positiveSheafOfModules (grading I) 3)
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell)
      (Spec.map (CommRingCat.ofHom g)))
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeLinearChartUnitIso I ell)
    (cubicClosedPointSerreSurfaceJetCotangent_positiveIdealLinearChartIso_toUnit I ell g)
    ((positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading I) 3 q))
    (Away.mk (grading I) ell.2 3 (q : CoordinateRing I) (by simpa using q.2))
    (cubicClosedPointSerreSurfaceJetCotangent_positiveLinearSectionCoefficient I ell q)

end PfaffianDescent

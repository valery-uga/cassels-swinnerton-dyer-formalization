import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveLinearChartLift
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveLinearSectionCoefficient

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The SAME closed subscheme, presented by its actual affine-chart ring map. -/
abbrev cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B] (g : Away (grading I) (ell : CoordinateRing I) →+* B) :=
  (Spec.map (CommRingCat.ofHom g) ≫
    (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 Nat.zero_lt_one).inv) ≫
    (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι

/-- A homogeneous cubic vanishing at the SAME actual closed subscheme has
a unique actual GLOBAL ideal-twist lift. The only vanishing premise is the
literal ring equation g(q/ell³)=0. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_globalLift
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B] (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (q : grading I 3)
    (hq : g (Away.mk (grading I) ell.2 3 (q : CoordinateRing I)
      (by simpa using q.2)) = 0) :
    ∃! v : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
      closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
        (positiveSheafOfModules (grading I) 3),
      v ≫ cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g) =
      (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) 3 q) := by
  let h : RingHom.ker g := ⟨Away.mk (grading I) ell.2 3 (q : CoordinateRing I)
    (by simpa using q.2), hq⟩
  let s := (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
    (positiveGlobalSectionOfHomogeneous (grading I) 3 q)
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
  exact cubicClosedPointSerreSurfaceJetCotangent_positiveLinearChart_globalLift I ell g s t
    ((cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom_toUnit g h).trans hb.symm)

end PfaffianDescent

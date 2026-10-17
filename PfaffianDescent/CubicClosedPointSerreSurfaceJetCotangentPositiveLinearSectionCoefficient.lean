import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveSectionCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentRefinedSectionCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentLinearChartFunction

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- On the literal affine chart, the actual global cubic has coefficient
the literal q/ell³ element, under the native positive-three unit. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveLinearSectionCoefficient
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (q : grading I 3) :
    unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso
          (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).inv ≫
        (Scheme.Modules.restrictFunctor
          (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).map
          ((positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
            (positiveGlobalSectionOfHomogeneous (grading I) 3 q)) ≫
        (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeLinearChartUnitIso I ell).hom) =
    (affineGlobalSectionsUnitLinearEquiv
      (A := Away (grading I) (ell : CoordinateRing I))).symm
      (Away.mk (grading I) ell.2 3 (q : CoordinateRing I) (by simpa using q.2)) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let e := Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 Nat.zero_lt_one
  let T := positiveSheafOfModules (grading I) 3
  let p := cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell
  let s := positiveGlobalSectionOfHomogeneous (grading I) 3 q
  have hu := cubicClosedPointSerreSurfaceJetCotangent_sectionChartCoefficient U T p s
  have hq := cubicClosedPointSerreSurfaceJetCotangent_positiveSectionCoefficient I ell q
  have hlocal := hu.trans (congrArg (fun r => U.topIso.inv r) hq)
  have hr := cubicClosedPointSerreSurfaceJetCotangent_refinedSectionCoefficient e.inv U.ι T p
    (T.unitHomEquiv.symm s)
  have h := hr.trans (congrArg (fun r => e.inv.appTop r) hlocal)
  exact h.trans (cubicClosedPointSerreSurfaceJetCotangent_linearChartFunction I ell _)

end PfaffianDescent

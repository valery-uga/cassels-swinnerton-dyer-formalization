import PfaffianDescent.ActualOriginalIdealQuadraticChartCoefficient
import PfaffianDescent.ActualOriginalIdealQuadraticNativeRestriction

/- SOURCE ONLY / UNVERIFIED. Internally chosen SAME original quartic-point
chart: actual ideal section coefficient agrees with the prior literal native
quadratic restriction. This is a derived coefficient comparison. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma actualOriginalAmbientIdealQuadraticChosenChartCoefficient
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
    actualOriginalAmbientIdealQuadraticChartCoefficient p hp P C.index s =
      (Proj.awayToSection (grading I) (coordinate I C.index)).hom
        (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion (quotientProjMap I) := quotientProjMap_isClosedImmersion I
  letI : IsClosedImmersion (q ≫ quotientProjMap I) := IsClosedImmersion.comp q _
  letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
  have h := actualOriginalAmbientIdealQuadraticChartCoefficient_eq_native p hp P C.index s
  change actualOriginalAmbientIdealQuadraticChartCoefficient p hp P C.index s =
    (Proj.awayToSection (grading I) (coordinate I C.index)).hom
      (MvPolynomial.aeval (chartCoordinate I C.index)
        (p3ActualIdealQuadraticIntrinsicLinearEquiv
          (q ≫ quotientProjMap I) s).val)
  exact h

end PfaffianDescent

import PfaffianDescent.ActualGlobalPositiveTwistConormalDifferentialMap
import PfaffianDescent.ActualOriginalAmbientIdealQuadraticNativeTwistRestriction

/- SOURCE ONLY / UNVERIFIED. Canonical original quadratic Phi is defined
through the genuinely GLOBAL conormal universal differential and ACTUAL O2
pullback/tensor maps. Domain is genuine AMBIENT H0(P3,I_(P,P3)(2)). It first
restricts into the actual cubic ideal. No chosen-chart comparison is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalGlobalCanonicalQuadraticPhi
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
          (positiveSheafOfModules (grading (equationIdeal p hp)) 2))) := by
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)
  exact (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).map
    (actualGlobalPositiveTwistConormalDifferentialMap I q 2)
    (actualModulePointSectionClass q M
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s))

end PfaffianDescent

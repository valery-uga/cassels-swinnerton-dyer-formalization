import PfaffianDescent.ActualOriginalIdealTwistSourceRefinement
import PfaffianDescent.ActualOriginalNativeIdealTwistConstructedChartIso
import PfaffianDescent.ActualOriginalQuarticCotangentChartChoice
import PfaffianDescent.ActualPositiveTwistChartUnit

/- SOURCE ONLY / UNVERIFIED. Actual original cubic/closed quartic point:
its native O2 ideal-twist chart Iso uses the SAME original residue morphism.
Every source square and closedness instance is internally derived. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalNativeIdealTwistChartIso
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (Scheme.Modules.restrictFunctor (chartι I C.index)).obj
      (closedImmersionIdealTwist q (positiveSheafOfModules (grading I) 2)) ≅
    closedImmersionModule (Spec.map (CommRingCat.ofHom C.residue)) :=
  actualOriginalNativeIdealTwistConstructedChartIso p hp P
    (actualOriginalQuarticCotangentChartChoice p hp P hP)

end PfaffianDescent

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual original quartic point chooses its chart internally;
this direct specialization keeps the inferred native inclusion proof. -/
def actualOriginalNativeIdealTwistChartIso_toInclusion
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :=
  actualOriginalNativeIdealTwistConstructedChartIso_toInclusion p hp P
    (actualOriginalQuarticCotangentChartChoice p hp P hP)

end PfaffianDescent

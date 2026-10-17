import PfaffianDescent.ActualIntrinsicQuadraticNativeResidueZero
import PfaffianDescent.ActualOriginalQuarticCotangentChartChoice
import PfaffianDescent.ActualP3QuadraticRestrictionChartComparison
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/- SOURCE ONLY / UNVERIFIED. GENUINE original H0(I_P(2)) is restricted to
one internally derived actual native chart, with residue vanishing PROVED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ActualOriginalPointIdealQuadraticSections
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :=
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
    (closedImmersionIdealTwist
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
      (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))

def actualOriginalPointIdealQuadratic_nativeRestriction
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    letI : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
      (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    ActualOriginalPointIdealQuadraticSections p hp P →ₗ[K]
      ChartRing (equationIdeal p hp) C.index := by
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  letI : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
    (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  let E := p3ActualIdealQuadraticIntrinsicLinearEquiv
    ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
  exact ((aeval (R := K) (chartCoordinate (equationIdeal p hp) C.index)).toLinearMap.comp
    (intrinsicFullQuadraticSystem
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))).subtype).comp
        E.toLinearMap

theorem actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    (actualOriginalQuarticCotangentChartChoice p hp P hP).residue
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) = 0 := by
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let E := p3ActualIdealQuadraticIntrinsicLinearEquiv
    ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp))
  exact actualIntrinsicQuadratic_nativeResidue_zero p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
      (E s).val (E s).property

end PfaffianDescent

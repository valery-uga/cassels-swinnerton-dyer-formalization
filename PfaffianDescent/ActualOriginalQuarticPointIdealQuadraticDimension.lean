import PfaffianDescent.NormalizedBasisQuadraticRestriction
import PfaffianDescent.ActualOriginalIdealQuadraticNativeRestriction
import PfaffianDescent.ActualNativeChartNormalizedAlgebraPoint
import PfaffianDescent.PerfectFieldQuarticPointChartBasis

/- SOURCE ONLY / UNVERIFIED. Genuine original H0(I_P(2)) has dimension6,
derived from actual geometric spanning and actual degree4, not a certificate
or a coordinate space renamed H0. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem perfectField_originalQuarticPointIdealQuadratic_finrank_six
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (hspan : ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField P.1)) :
    finrank K (ActualOriginalPointIdealQuadraticSections p hp P) = 6 := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let I := equationIdeal p hp
  let L : Type u := (hypersurface p hp).residueField P.1
  let qP := (hypersurface p hp).fromSpecResidueField P.1
  letI : IsClosedImmersion (quotientProjMap I) := quotientProjMap_isClosedImmersion I
  letI : IsClosedImmersion (qP ≫ quotientProjMap I) := IsClosedImmersion.comp qP (quotientProjMap I)
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  have h4 : finrank K L = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) P).trans hP
  have hLI := perfectField_quartic_fieldPoint_chart_coordinates_independent (K := K) (L := L) I qP
    (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase p hp) P.1).symm
    h4 hspan C.index C.residue C.base C.factorization
  let b : Basis (Fin 4) K L := basisOfLinearIndependentOfCardEqFinrank hLI (by simp [h4])
  have hb (r : Fin 4) : b r = C.residue (chartCoordinate I C.index r) :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hLI (by simp [h4])) r
  have hj : b C.index = 1 := by rw [hb, chartCoordinate_self, map_one]
  have heq : intrinsicFullQuadraticSystem (qP ≫ quotientProjMap I) =
      homogeneousVanishingPolynomialSubmodule (K := K) b 2 := by
    ext Q
    dsimp only [qP]
    rw [← C.factorization, actualNativeChart_intrinsicQuadratic_mem_iff I C.index
      C.residue C.base Q, mem_homogeneousVanishingPolynomialSubmodule_iff]
    rw [hom_eval₂, C.base]
    exact (congrArg (fun x : Fin 4 → L =>
      Q.IsHomogeneous 2 ∧ eval₂ (algebraMap K L) x Q = 0)
      (funext (fun r => (hb r).symm))).to_iff
  change finrank K (SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
    (closedImmersionIdealTwist (qP ≫ quotientProjMap I)
      (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) = 6
  rw [p3ActualIdealQuadratic_finrank_eq_intrinsic, heq]
  exact normalizedBasis_homogeneousQuadraticVanishing_finrank_six b C.index hj

end PfaffianDescent

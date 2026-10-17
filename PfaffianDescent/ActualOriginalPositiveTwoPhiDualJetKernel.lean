import PfaffianDescent.ActualOriginalIdealQuadraticPositiveTwoPhi

/- SOURCE ONLY / UNVERIFIED. EXACT native dual jet test for every actual
original quadratic ideal section and arbitrary genuine Omega(2) quotient.
Residue-zero is derived from actual H0 membership, never assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoPhi_dualJet_zero_iff
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (actualCubicPositiveTwoDifferentials p hp)) →ₗ[(hypersurface p hp).residueField P.1]
          (hypersurface p hp).residueField P.1)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let R := ChartRing (equationIdeal p hp) C.index
    let L := (hypersurface p hp).residueField P.1
    letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
    letI : SMul K R := aK.toSMul
    letI : Algebra R L := C.residue.toAlgebra
    letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
      (fun c => (RingHom.congr_fun C.base c).symm)
    let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
      ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
    actualKaehlerLineDualAlgebraMap (ell.comp E.symm.toLinearMap)
      (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s) = 0 ↔
        ell (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) = 0 := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  let L := (hypersurface p hp).residueField P.1
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  rw [actualResidueDualJet_zero_iff_on_vanishing_section _ _
    (actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s)]
  rfl

end PfaffianDescent

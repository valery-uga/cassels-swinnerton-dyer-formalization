import PfaffianDescent.ActualOpenImmersionDifferentialSheafIso
import PfaffianDescent.ActualOriginalPositiveTwoPointContraction
import PfaffianDescent.ActualModulePointChartSourceFactorization
import PfaffianDescent.ActualAffineSchemeDifferentialPointFiber
import PfaffianDescent.ActualCubicPositiveTwoChartContractedNativeDifferentialMap

/- SOURCE ONLY / UNVERIFIED contingency028. Actual original Omega(2) fiber -> native
Kaehler fiber, via TRUE original O2 contraction, true untwisted Omega
chart/source factorization and actual affine field-point equivalence.
No target-fiber/desired-map certificate. This definition does not yet
identify the separately constructed native Omega(2) equivalence. Its
VALUE now applies the shared arbitrary-chart factory to the SAME original
chart choice, residue factorization and internally derived O2 Iso. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalPositiveTwoContractedNativeDifferentialMap
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let L := (hypersurface p hp).residueField P.1
    let R := ChartRing I C.index
    letI : Algebra K R := (chartBaseMap I C.index).toAlgebra
    letI : Algebra R L := C.residue.toAlgebra
    let q := (hypersurface p hp).fromSpecResidueField P.1
    (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback q).obj
        (schemeModuleTensor (schemeRelativeDifferentials (toBase I))
          (positiveSheafOfModules (grading I) 2))) →ₗ[L]
            (L ⊗[R] KaehlerDifferential K R) := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  exact actualCubicPositiveTwoChartContractedNativeDifferentialMap p hp
    C.index C.residue ((hypersurface p hp).fromSpecResidueField P.1)
    C.factorization (actualOriginalPositiveTwoPointTrivialization p hp P hP)

end PfaffianDescent

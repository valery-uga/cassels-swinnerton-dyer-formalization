import PfaffianDescent.ActualOriginalQuarticPointIdealQuadraticDimension
import PfaffianDescent.ActualCubicPositiveTwoDifferentialPointFiber
import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhiLinear
import PfaffianDescent.QuarticDualKernelDimension

/-! The literal lower bound dim ker(Phi dual) >= 2 on the genuine global
quadratic-section map. Dimensions are derived from the original geometry.
Source draft; no acceptance of the imported pending geometry is implied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem perfectField_originalGlobalCanonicalPhi_dual_kernel_finrank_at_least_two
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (hspan : ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField P.1)) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (actualCubicPositiveTwoDifferentials p hp))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    2 ≤ finrank K (LinearMap.ker
      (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P).dualMap) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  let L := (hypersurface p hp).residueField P.1
  let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (actualCubicPositiveTwoDifferentials p hp))
  let V := ActualOriginalPointIdealQuadraticSections p hp P
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  have hE : finrank L E2 = 2 :=
    smoothCubic_originalPositiveTwoDifferentialFiber_finrank_two (K := K) (L := L) p hp hp0
      ((hypersurface p hp).fromSpecResidueField P.1)
      (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase p hp) P.1).symm
  have hV : finrank K V = 6 :=
    perfectField_originalQuarticPointIdealQuadratic_finrank_six p hp P hP hspan
  letI : FiniteDimensional L E2 := FiniteDimensional.of_finrank_pos (by rw [hE]; decide)
  letI : FiniteDimensional K E2 := Module.Finite.trans L E2
  letI : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by rw [hV]; decide)
  have hL : finrank K L = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) P).trans hP
  have hEK : finrank K E2 = 8 := by
    rw [← Module.finrank_mul_finrank K L E2, hL, hE]
  exact QuarticNet.dualMap_kernel_finrank_at_least_two
    (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P) hEK hV

end PfaffianDescent

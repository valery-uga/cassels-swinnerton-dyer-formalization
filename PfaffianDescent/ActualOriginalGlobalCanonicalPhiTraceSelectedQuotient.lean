import PfaffianDescent.ActualOriginalQuarticPointIdealQuadraticDimension
import PfaffianDescent.ActualOriginalPositiveTwoTraceDuality
import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhiLinear

/- SOURCE ONLY / UNVERIFIED. Trace selection is instantiated DIRECTLY on the genuine GLOBAL Phi, with genuine
original V=H0(I_P(2)) and E=Omega(2)|P, with real dimensions internally
proved from actual original geometric spanning and smoothness. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem perfectField_originalGlobalCanonicalPhi_traceSelectedQuotient
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
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    ∃ ell : E2 →ₗ[L] L, Function.Surjective ell ∧
      (Algebra.trace K L).comp ((ell.restrictScalars K).comp
        (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)) = 0 ∧
      3 ≤ finrank K (LinearMap.ker ((ell.restrictScalars K).comp
        (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P))) := by
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
  exact QuarticNet.quotient_with_large_kernel
    (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P) hL hE hV

end PfaffianDescent

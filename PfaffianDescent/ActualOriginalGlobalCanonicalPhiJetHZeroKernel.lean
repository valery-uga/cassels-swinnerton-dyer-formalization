import PfaffianDescent.ActualOriginalGlobalCanonicalQuadraticPhiNativeEquality
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetHZeroKernel
import Mathlib.Algebra.Module.Submodule.Equiv

/- SOURCE ONLY / UNVERIFIED. Literal genuine AMBIENT H0(I_Zell(2)) is
the kernel of ell composed with genuinely GLOBAL canonical Phi, for EVERY
surjective actual Omega(2) line quotient. The SAME original embedded dual
jet, full nilpotent ideal and canonical H0 inclusion are retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualOriginalGlobalCanonicalPhiJet_quadratic_mem_iff
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
      isClosed_singleton_iff_isClosedImmersion.mp P.2
    (p3ActualIdealQuadraticIntrinsicLinearEquiv
      ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap (equationIdeal p hp)) s).val ∈
      intrinsicFullQuadraticSystem
        (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫
          quotientProjMap (equationIdeal p hp)) ↔
      ell (actualOriginalGlobalCanonicalQuadraticPhi p hp P s) = 0 := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  have h := actualOriginalPositiveTwoNativeJet_quadratic_mem_iff p hp P hP ell s
  rw [← actualOriginalGlobalCanonicalQuadraticPhi_eq_native p hp P hP s] at h
  exact h

def actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := ActualOriginalPositiveTwoFiber p hp P
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    letI : IsClosedImmersion d :=
      (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2)) ≃ₗ[K]
      LinearMap.ker ((ell.restrictScalars K).comp
        (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let E2 := ActualOriginalPositiveTwoFiber p hp P
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d :=
    (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
  let tNative := (ell.restrictScalars K).comp
    (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP)
  let tGlobal := (ell.restrictScalars K).comp
    (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)
  have hk : LinearMap.ker tNative = LinearMap.ker tGlobal := by
    dsimp only [tNative, tGlobal]
    rw [actualOriginalGlobalCanonicalQuadraticPhi_eq_native_linearMap p hp P hP]
  exact (actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell).trans
    (LinearEquiv.ofEq _ _ hk)

end PfaffianDescent

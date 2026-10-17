import PfaffianDescent.ActualOriginalGlobalCanonicalPhiTraceSelectedQuotient
import PfaffianDescent.ActualOriginalGlobalCanonicalPhiJetHZeroKernel

/- SOURCE ONLY / UNVERIFIED. GENUINE GLOBAL canonical-Phi trace argument: the same chosen
quotient yields an original cubic tangent jet and at least three genuine
ideal-sheaf quadratic sections. No arbitrary quotient is promised this
inequality. The global conormal/native identification is derived by the imported
proved comparisons. Universal supplied-Z inverse classification remains separate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem perfectField_originalGlobalTraceSelectedJet_hZero_three
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (hspan : ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField P.1)) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := ActualOriginalPositiveTwoFiber p hp P
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    ∃ ell : E2 →ₗ[L] L, ∃ hell : Function.Surjective ell,
      (Algebra.trace K L).comp ((ell.restrictScalars K).comp
        (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)) = 0 ∧
      let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
      letI : IsClosedImmersion d :=
        (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
      IsClosedImmersion d ∧
      (∃ hf : IsFinite (d ≫ hypersurfaceToBase p hp), Set.range d = {P.1} ∧
        @AllCharacteristics.finiteSchemeRank K _ _ (d ≫ hypersurfaceToBase p hp) hf = 8) ∧
      3 ≤ finrank K (SchemeModuleGlobalSectionsOver
        (ambientToBase (R := K) (σ := Fin 4))
        (closedImmersionIdealTwist (d ≫ quotientProjMap (equationIdeal p hp))
          (ProjectiveNegativeTwist.positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2))) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let E2 := ActualOriginalPositiveTwoFiber p hp P
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  obtain ⟨ell, hell, htrace, hker⟩ :=
    perfectField_originalGlobalCanonicalPhi_traceSelectedQuotient p hp hp0 P hP hspan
  have hJet := actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell
  refine ⟨ell, hell, htrace, ?_⟩
  dsimp only
  let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  letI : IsClosedImmersion d := hJet.1
  refine ⟨hJet.1, hJet.2, ?_⟩
  rw [(actualOriginalGlobalCanonicalPhiJetHZeroKernelEquiv p hp P hP ell hell).finrank_eq]
  exact hker

end PfaffianDescent

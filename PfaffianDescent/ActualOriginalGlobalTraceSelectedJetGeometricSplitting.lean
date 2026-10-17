import PfaffianDescent.ActualOriginalGlobalTraceSelectedJetHZeroThree
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetGeometricSplitting

/- SOURCE ONLY / UNVERIFIED. Thin SAME-witness conjunction: include the
actual algebraic-closure splitting required by literal prop:existence-of-Z. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem perfectField_originalGlobalTraceSelectedJet_hZero_three_geometric_split
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
          (ProjectiveNegativeTwist.positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) ∧
    ∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
      Nonempty (pullback
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
        (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫ hypersurfaceToBase p hp) ≅
        ∐ fun _ : J => Spec (.of (DualNumber (AlgebraicClosure K)))) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let L := (hypersurface p hp).residueField P.1
  let E2 := ActualOriginalPositiveTwoFiber p hp P
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  obtain ⟨ell, hell, htrace, hclosed, hfinite, hzero⟩ :=
    perfectField_originalGlobalTraceSelectedJet_hZero_three p hp hp0 P hP hspan
  exact ⟨ell, hell, htrace, hclosed, hfinite, hzero,
    actualOriginalPositiveTwoNativeJetEmbedding_geometric_split p hp P hP ell hell⟩

end PfaffianDescent

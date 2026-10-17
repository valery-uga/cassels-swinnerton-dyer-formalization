import PfaffianDescent.ActualOriginalQuarticRetainedAffineGlobalPhiTraceJet
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetGeometricSplitting

/- SOURCE ONLY / UNVERIFIED. Thin SAME-witness conjunction: include the
actual algebraic-closure splitting required by literal prop:existence-of-Z. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem perfectField_originalQuartic_retainedAffineGlobalPhiTraceJet_geometric_split
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
    let I := equationIdeal p hp
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
    ∃ b : Basis (Fin 4) K L,
      (∀ r, b r = C.residue (chartCoordinate I C.index r)) ∧
      let sigma := Equiv.swap (0 : Fin 4) C.index
      let b' := b.reindex sigma
      let c := fun a : Fin 3 => b' a.succ
      let F := QuarticNet.dehomogenizeAtZero (rename sigma p)
      ∃ q : Module.Dual L (LinearMap.ker (QuarticNet.affineDifferential c F)) →ₗ[L] L,
        Function.Surjective q ∧
        (Algebra.trace K L).comp ((q.restrictScalars K).comp
          (QuarticNet.affineQuadricCotangentRestriction c F)) = 0 ∧
        ∃ phi : ChartRing I C.index →ₐ[K] DualNumber L,
          Function.Surjective phi ∧
          (∀ r, (phi r).fst = C.residue r) ∧
          (∀ Q : QuarticNet.affineQuadricsThroughPoint (k := K) c,
            (phi ((rename sigma.symm (QuarticNet.homogeneousAffineQuadrics Q.val)).eval₂
              (chartBaseMap I C.index) (chartCoordinate I C.index))).snd =
              q (QuarticNet.affineQuadricCotangentRestriction c F Q)) ∧
          ∃ ell : E2 →ₗ[L] L, ∃ hell : Function.Surjective ell,
            (Algebra.trace K L).comp ((ell.restrictScalars K).comp
              (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P)) = 0 ∧
            actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell =
              Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ chartι I C.index ∧
            (∀ s : ActualOriginalPointIdealQuadraticSections p hp P,
              ell (actualOriginalGlobalCanonicalQuadraticPhiLinearMap p hp P s) =
                (phi (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)).snd) ∧
            let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
            letI : IsClosedImmersion d :=
              (actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell hell).1
            IsClosedImmersion d ∧
            (∃ hf : IsFinite (d ≫ hypersurfaceToBase p hp), Set.range d = {P.1} ∧
              @AllCharacteristics.finiteSchemeRank K _ _ (d ≫ hypersurfaceToBase p hp) hf = 8) ∧
            3 ≤ finrank K (SchemeModuleGlobalSectionsOver
              (ambientToBase (R := K) (σ := Fin 4))
              (closedImmersionIdealTwist
                (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫ quotientProjMap I)
                (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) ∧
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
  let I := equationIdeal p hp
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
  obtain ⟨b, hb, q, hq, htraceQ, phi, hphi, hred, hCoeff, ell, hell,
    htrace, hembed, hCoefficient, hclosed, hfinite, hzero⟩ :=
    perfectField_originalQuartic_retainedAffineGlobalPhiTraceJet p hp hp0 P hP hspan
  exact ⟨b, hb, q, hq, htraceQ, phi, hphi, hred, hCoeff, ell, hell,
    htrace, hembed, hCoefficient, hclosed, hfinite, hzero,
    actualOriginalPositiveTwoNativeJetEmbedding_geometric_split p hp P hP ell hell⟩

end PfaffianDescent

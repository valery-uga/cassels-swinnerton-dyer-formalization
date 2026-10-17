import PfaffianDescent.ActualFixedNativeChartRetainedAffineTraceJet
import PfaffianDescent.ActualOriginalPositiveTwoLineFromNativeDualMap
import PfaffianDescent.ActualOriginalQuarticPointIdealQuadraticDimension

/- SOURCE ONLY / UNVERIFIED. SAME original P/cubic/native chart, SAME
AFFINE trace-selected q/v and SAME actual native dual jet. Every final
chart/basis/residue/differential/ambient/trace comparison is derived from
primitive original hypotheses. No independent opaque trace witness is used. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem perfectField_originalQuartic_retainedAffinePhiTraceJet
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
          ∃ ell : E2 →ₗ[L] L, Function.Surjective ell ∧
            (Algebra.trace K L).comp ((ell.restrictScalars K).comp
              (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP)) = 0 ∧
            actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell =
              Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ chartι I C.index ∧
            (∀ s : ActualOriginalPointIdealQuadraticSections p hp P,
              ell (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) =
                (phi (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)).snd) ∧
            3 ≤ finrank K (SchemeModuleGlobalSectionsOver
              (ambientToBase (R := K) (σ := Fin 4))
              (closedImmersionIdealTwist
                (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫ quotientProjMap I)
                (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) := by
  classical
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  letI : IsClosedImmersion ((hypersurface p hp).fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  let L := (hypersurface p hp).residueField P.1
  let E2 := ActualOriginalPositiveTwoFiber p hp P
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  let I := equationIdeal p hp
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  letI : Algebra K (ChartRing I C.index) := (chartBaseMap I C.index).toAlgebra
  have h4 : finrank K L = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) P).trans hP
  have hLI := perfectField_quartic_fieldPoint_chart_coordinates_independent I
    ((hypersurface p hp).fromSpecResidueField P.1)
    (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase p hp) P.1).symm
    h4 hspan C.index C.residue C.base C.factorization
  let b : Basis (Fin 4) K L := basisOfLinearIndependentOfCardEqFinrank hLI (by simp [h4])
  have hb (r : Fin 4) : b r = C.residue (chartCoordinate I C.index r) :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hLI (by simp [h4])) r
  obtain ⟨q, hq, htraceQ, phi, hphi, hred, hTraceAll, hCoeff⟩ :=
    actualFixedNativeChart_exists_retainedAffineTraceJet p hp hp0 C.index C.residue C.base b hb
  let ell := actualOriginalPositiveTwoLineFromNativeDualMap p hp P hP phi hred
  have hell : Function.Surjective ell :=
    actualOriginalPositiveTwoLineFromNativeDualMap_surjective p hp P hP phi hred hphi
  let EP := p3ActualIdealQuadraticIntrinsicLinearEquiv
    ((hypersurface p hp).fromSpecResidueField P.1 ≫ quotientProjMap I)
  have hCoefficient (s : ActualOriginalPointIdealQuadraticSections p hp P) :
      ell (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) =
        (phi (actualOriginalPointIdealQuadratic_nativeRestriction p hp P hP s)).snd :=
    actualOriginalPositiveTwoLineFromNativeDualMap_Phi_coefficient p hp P hP phi hred s
  have hTracePhi : (Algebra.trace K L).comp ((ell.restrictScalars K).comp
      (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP)) = 0 := by
    ext s
    change Algebra.trace K L (ell (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s)) = 0
    rw [hCoefficient]
    exact hTraceAll (EP s).val (EP s).property.1
      (actualOriginalPointIdealQuadratic_nativeRestriction_residue_zero p hp P hP s)
  let V := ActualOriginalPointIdealQuadraticSections p hp P
  have hV : finrank K V = 6 :=
    perfectField_originalQuarticPointIdealQuadratic_finrank_six p hp P hP hspan
  letI : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by rw [hV]; decide)
  let t := (ell.restrictScalars K).comp (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP)
  have hproper : LinearMap.range t ≠ ⊤ := by
    intro htop
    have hts : Function.Surjective t := LinearMap.range_eq_top.mp htop
    apply Algebra.trace_ne_zero K L
    ext z
    obtain ⟨s, rfl⟩ := hts z
    exact congrArg (fun m : V →ₗ[K] K => m s) hTracePhi
  have hlt : finrank K (LinearMap.range t) < 4 := by
    simpa [h4] using Submodule.finrank_lt hproper
  have hdim := t.finrank_range_add_finrank_ker
  rw [hV] at hdim
  have hker : 3 ≤ finrank K (LinearMap.ker t) := by omega
  have hHZero : 3 ≤ finrank K (SchemeModuleGlobalSectionsOver
      (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist
        (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫ quotientProjMap I)
        (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) := by
    rw [(actualOriginalPositiveTwoNativeJetHZeroKernelEquiv p hp P hP ell hell).finrank_eq]
    exact hker
  exact ⟨b, hb, q, hq, htraceQ, phi, hphi, hred, hCoeff, ell, hell, hTracePhi,
    actualOriginalPositiveTwoLineFromNativeDualMap_embedding p hp P hP phi hred,
    hCoefficient, hHZero⟩

end PfaffianDescent

import PfaffianDescent.CorayOriginalAuxiliaryGeometricPairSameGraph
import PfaffianDescent.CorayOriginalRankThreeAuxiliaryGeometricEnumeration
import PfaffianDescent.CorayOriginalUniformRankThreeGeometricPointTangentSection
import PfaffianDescent.CorayNativeFixedWholePairGraphGuard

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- ONE original joint Q/v/F tuple and its full-kernel polynomial, together
with the SAME constructed literal auxiliary degree3 cut on the selected
original graph, construct an ORIGINAL-K tangent section. Finite etaleness,
ALLpoints enumeration, normalized distinct pair, protected rank/pivot,
annihilator and nonzero pair value are derived internally. No supplied
embedding list, distinctness, nonzero minor, desired jet/section outcome,
change of original K, or new existential Q/F is used. -/
theorem cubicOriginalSelectedAuxiliary_sameJointGuard_exists_originalTangentSection001
    {K L B M : Type u} [Field K] [CharZero K] [Field L] [CommRing B] [Field M]
    [Algebra K L] [Algebra K B] [Algebra K M] [Module.Finite K B] [IsSepClosed M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) {m : ℕ}
    (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (q : Fin m → MvPolynomial (Fin 4) K)
    (hRep : ∀ t, Ideal.Quotient.mk (equationIdeal p hp).toIdeal (q t) = (b t).1.1)
    (rankPivot pairPivot : Fin 3) (a i k : Fin m)
    (H : ChartRing (equationIdeal p hp) j)
    (hRank : originalNativeProjection_rankTwoOnPrincipalOpen p hp j rankPivot
      (fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)) a i k H)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (T : Matrix (Fin 2) (Fin 2) K)
    (hField : IsField B) (hDegree : finrank K B = 3) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let f : Fin m → R := fun t => e (b t)
    let x := chartCoordinate (equationIdeal p hp) j
    let gradient : Fin 3 → R := fun l => (pderiv (j.succAbove l) p).eval₂ (algebraMap K R) x
    ∀ (A : Fin m → R) (v : R),
    (∀ h : R →ₐ[K] M, h v ≠ 0 →
      h H ≠ 0 ∧ h (gradient pairPivot) ≠ 0 ∧
      (∑ t, h (A t) • (q t).eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates (fun l => h (x l))
          (fun r l => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            (fun s => h (gradient s)) pairPivot l r))) = 0) →
    ∀ bad : GrassmannianChartRing K 2 2,
    (let Q : R ⊗[K] R := ∑ t, A t ⊗ₜ[K] f t
     let F := Q * (v ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] v)
     let D := (R ⊗[K] R) ⧸ Ideal.span ({F} : Set (R ⊗[K] R))
     let mk : R ⊗[K] R →+* D := Ideal.Quotient.mk (Ideal.span ({F} : Set (R ⊗[K] R)))
     let xy := cubicOriginalWholePairChartAmbientVectors p hp j
     let xx := graphCoefficientMap mk xy.1
     let yy := graphCoefficientMap mk xy.2
     let minor := originalPairGrassmannMinor rho xx yy
     let C := Localization.Away minor
     let xC := graphCoefficientMap (algebraMap D C) (graphCoordinatePermutation D rho xx)
     let yC := graphCoefficientMap (algebraMap D C) (graphCoordinatePermutation D rho yy)
     let N := originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf minor)
     (MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => N ij.1 ij.2)) bad = 0) →
    MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2) bad ≠ 0 →
    ∀ hB : R →ₐ[K] B, Function.Surjective hB →
      (finiteProductCoordinateEquiv (R := B) 2 2).symm (fun l => hB (x l)) ∈
        grassmannianChartSubmodule B rho (T.map (algebraMap K B)) →
    ∃ (hFT : Algebra.FiniteType K B) (hEtale : Algebra.FormallyEtale K B),
      letI : Algebra.FiniteType K B := hFT
      letI : Algebra.FormallyEtale K B := hEtale
      ∃ points : Fin 3 ≃ PrimeSpectrum (M ⊗[K] B),
      let sigma0 := originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) (points 0)
      let h := sigma0.comp hB
      let z : Fin 4 → M := fun l => h (x l)
      let vv : Fin 2 → Fin 4 → M := fun r l =>
        PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j (fun s => h (gradient s)) pairPivot l r
      ∃ (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z vv) = 0)
        (hAnchor : surfacePlaneJetCoordinates z vv j = 1),
      let gJ := cubicNormalizedFullJetChartMap p hp j z vv hpJ hAnchor
      ∃ c : Fin m → K,
        let s : cubicThroughCoordinateSections p hp n y hpy := ∑ t, c t • b t
        hB (e s) = 0 ∧ gJ (e s) ≠ 0 ∧ (gJ (e s)).snd ≠ 0 := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let f : Fin m → R := fun t => e (b t)
  let x := chartCoordinate (equationIdeal p hp) j
  let gradient : Fin 3 → R := fun l => (pderiv (j.succAbove l) p).eval₂ (algebraMap K R) x
  dsimp only
  intro A v hPoints bad hKernel hBad hB hSurj hGraph
  obtain ⟨hFT, hEtale⟩ := originalFiniteAuxiliaryAlgebra_isField_finiteType_formallyEtale001 (K := K) hField
  letI : Algebra.FiniteType K B := hFT
  letI : Algebra.FormallyEtale K B := hEtale
  obtain ⟨points⟩ := originalFiniteAuxiliaryAlgebra_isField_rankThree_exists_actualGeometricEnumeration001
    (K := K) (M := M) hField hDegree
  let sigma0 := originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) (points 0)
  let sigma1 := originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) (points 1)
  let h0 := sigma0.comp hB
  let h1 := sigma1.comp hB
  let z : Fin 4 → M := fun l => h0 (x l)
  let vv : Fin 2 → Fin 4 → M := fun r l =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j (fun s => h0 (gradient s)) pairPivot l r
  let w : Fin m → SurfacePlaneJet M := fun t =>
    (q t).eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z vv)
  obtain ⟨hx, hy, hEllx, hElly, hNe, _hMinor⟩ :=
    cubicOriginalAuxiliaryGeometricEnumeration_actualTensorPair_distinct_sameOriginalGraph001
      p hp j rho T hB hSurj hGraph points
  have hBadM : (MvPolynomial.aeval (R := K)
      (fun ij : Fin 2 × Fin 2 => (T.map (algebraMap K M)) ij.1 ij.2)) bad ≠ 0 := by
    have hEval : algebraMap K M (MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2) bad) =
        (MvPolynomial.aeval (R := K)
          (fun ij : Fin 2 × Fin 2 => (T.map (algebraMap K M)) ij.1 ij.2)) bad := by
      rw [MvPolynomial.aeval_def]
      change algebraMap K M (bad.eval₂ (RingHom.id K)
        (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)) =
        bad.eval₂ (algebraMap K M) (fun ij : Fin 2 × Fin 2 => algebraMap K M (T ij.1 ij.2))
      have h := MvPolynomial.hom_eval₂ bad (RingHom.id K) (algebraMap K M)
        (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)
      rw [RingHom.comp_id] at h
      exact h
    rw [← hEval]
    simpa only [map_zero] using (algebraMap K M).injective.ne hBad
  have hNative : h0 v ≠ 0 → (∑ t, h0 (A t) • w t) = 0 := fun hv => (hPoints h0 hv).2.2
  have hGuard := nativeFixedWholePairKernelEquation_nonzero_on_sameGraph_excludes_badPair001
    A f v (cubicOriginalWholePairChartAmbientVectors p hp j) rho bad hKernel h0 h1 w hNative
    (T.map (algebraMap K M)) (originalAmbientCoordinateFunctional j)
    hx hy hEllx hElly hNe hBadM
  have hData := hPoints h0 hGuard.1
  have hPair : (∑ t, h0 (A t) * sigma1 (hB (e (b t)))) ≠ 0 := by
    simpa only [f, h1, AlgHom.comp_apply, map_sum, Algebra.TensorProduct.lift_tmul] using hGuard.2.2.2
  obtain ⟨hpJ, hAnchor, c, hAux, hNonzero, hTangent⟩ :=
    cubicThroughPointBasis_uniformRank_threeActualGeometricPoints_pairSeparation_exists_originalTangentSection001
      p hp n y hpy j b q hRep rankPivot pairPivot a i k H hRank hB points
      hData.1 hData.2.1 (fun t => h0 (A t)) hData.2.2 hPair
  exact ⟨hFT, hEtale, points, hpJ, hAnchor, c, hAux, hNonzero, hTangent⟩

end PfaffianDescent.Coray

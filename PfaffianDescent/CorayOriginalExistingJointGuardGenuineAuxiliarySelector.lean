import PfaffianDescent.CorayOriginalSameBasisRepresentativeFullGraphCut
import PfaffianDescent.CorayOriginalSelectedAuxiliaryJointGuardSection

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped TensorProduct PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Preserve ONE already constructed original pair/rank/Q/v/F/bad tuple.
The SAME basis denominator supplies q0; original-K matrix choice and
noSection construct its SAME literal AdjoinRoot cut/full-degree-three
original A. The full kernel on that SAME selected graph constructs an
ORIGINAL-K through-P/A tangent section. No second pair/principal choice,
selected matrix/field/point/section or geometric conclusion is supplied.
The final natural caller constructs rho alignment and this whole input
tuple internally, then invokes this genuine selection cut. -/
theorem cubicThroughPointBasis_existingJointGuard_exists_sameGraph_fullDegreeAuxiliary_originalTangentSection001
    {K L M : Type u} [Field K] [CharZero K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [IsSepClosed M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (hp0 : p ≠ 0)
    (hno : ¬ ∃ s : AlgebraicGeometry.Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange] {m : ℕ}
    (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (q : Fin m → MvPolynomial (Fin 4) K)
    (hRep : ∀ t, Ideal.Quotient.mk (equationIdeal p hp).toIdeal (q t) = (b t).1.1)
    (rankPivot pairPivot : Fin 3) (a i k : Fin m)
    (H : ChartRing (equationIdeal p hp) j)
    (hRank : originalNativeProjection_rankTwoOnPrincipalOpen p hp j rankPivot
      (fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)) a i k H)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (hRho : finSumFinEquiv (m := 2) (n := 2) (rho (Sum.inl (1 : Fin 2))) = j) :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let f : Fin m → R := fun t => e (b t)
    let x := chartCoordinate (equationIdeal p hp) j
    let gradient : Fin 3 → R := fun l => (pderiv (j.succAbove l) p).eval₂ (algebraMap K R) x
    ∀ (A : Fin m → R) (v : R), v ≠ 0 →
    (∀ h : R →ₐ[K] M, h v ≠ 0 →
      h H ≠ 0 ∧ h (gradient pairPivot) ≠ 0 ∧
      (∑ t, h (A t) • (q t).eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates (fun l => h (x l))
          (fun r l => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            (fun s => h (gradient s)) pairPivot l r))) = 0) →
    ∀ bad : GrassmannianChartRing K 2 2, bad ≠ 0 →
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
    ∃ q0 : MvPolynomial (Fin 4) K,
      q0.IsHomogeneous n ∧ q0.eval₂ (algebraMap K L) y = 0 ∧
      q0 ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal q0 = (b a).1.1 ∧
    ∃ T : Matrix (Fin 2) (Fin 2) K,
      MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2) bad ≠ 0 ∧
      ∃ (c : Cubic K 4) (hc : c.toMvPolynomial = p),
      let aCol := originalGrassmannChartLineColumn001 rho T 0
      let bCol := originalGrassmannChartLineColumn001 rho T 1
      let iPivot := originalGrassmannChartLinePivot001 rho 0
      let F := cubicLinePolynomial c aCol bCol
      let B := AdjoinRoot F
      let x : Fin 4 → B :=
        AdjoinRoot.root F • (fun k => algebraMap K B (aCol k)) +
          (fun k => algebraMap K B (bCol k))
      let ell : MvPolynomial (Fin 4) K := X j - C (aCol j) * X iPivot
      let I := equationIdeal p hp
      ∃ hBFinite : Module.Finite K B,
        letI := hBFinite
        ∃ hField : IsField B,
          letI : Field B := hField.toField
          ∃ (hell : ell.IsHomogeneous 1)
            (hxell : ell.eval₂ (algebraMap K B) x = 1)
            (heI : ∀ f ∈ I.toIdeal, f.eval₂ (algebraMap K B) x = 0),
          let r : Spec (.of B) ⟶ hypersurface p hp :=
            linearNormalizedPoint I x ell hell hxell heI
          x j = 1 ∧
          (finiteProductCoordinateEquiv (R := B) 2 2).symm x ∈
            grassmannianChartSubmodule B rho (T.map (algebraMap K B)) ∧
          IsClosedImmersion r ∧
          r ≫ hypersurfaceToBase p hp =
            Spec.map (CommRingCat.ofHom (algebraMap K B)) ∧
          Module.finrank K B = 3 ∧
          ∃ g : R →ₐ[K] B,
            (∀ k, g (chartCoordinate I j k) = x k) ∧
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ chartι I j = r ∧
            g (cubicThroughPointChartEvaluation p hp n y hpy j (b a)) ≠ 0 ∧
            g v ≠ 0 ∧ q0.eval₂ (algebraMap K B) x ≠ 0 ∧
            Function.Surjective g ∧
            ∃ originalA : closedPoints (hypersurface p hp),
              originalA.1 = r (IsLocalRing.closedPoint B) ∧
              IsIso (r.residueFieldMap (IsLocalRing.closedPoint B)) ∧
              (hypersurfaceToBase p hp).residueDegree originalA.1 = 3 ∧
            ∃ (hFT : Algebra.FiniteType K B) (hEtale : Algebra.FormallyEtale K B),
              letI : Algebra.FiniteType K B := hFT
              letI : Algebra.FormallyEtale K B := hEtale
              ∃ points : Fin 3 ≃ PrimeSpectrum (M ⊗[K] B),
              let sigma := originalFiniteEtaleGeometricPoint (K := K) (A := B) (M := M) (points 0)
              let h := sigma.comp g
              let z : Fin 4 → M := fun l => h (chartCoordinate I j l)
              let vv : Fin 2 → Fin 4 → M := fun r l =>
                PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
                  (fun s => h ((pderiv (j.succAbove s) p).eval₂ (algebraMap K R)
                    (chartCoordinate I j))) pairPivot l r
              ∃ (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z vv) = 0)
                (hAnchor : surfacePlaneJetCoordinates z vv j = 1),
              let gJ := cubicNormalizedFullJetChartMap p hp j z vv hpJ hAnchor
              ∃ coefficients : Fin m → K,
                let s : cubicThroughCoordinateSections p hp n y hpy := ∑ t, coefficients t • b t
                g (e s) = 0 ∧ gJ (e s) ≠ 0 ∧ (gJ (e s)).snd ≠ 0 := by
  let R := ChartRing (equationIdeal p hp) j
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let f : Fin m → R := fun t => e (b t)
  let x := chartCoordinate (equationIdeal p hp) j
  let gradient : Fin 3 → R := fun l => (pderiv (j.succAbove l) p).eval₂ (algebraMap K R) x
  dsimp only
  intro A v hv hPoints bad hBad hKernel
  obtain ⟨q0, hq0, hqThrough, hqFresh, hqClass, T, hTBad, c, hc,
      hBFinite, hField, hell, hxell, heI, hxj, hxGraph, hClosed, hBase,
      hRankB, g, hCoords, hFactor, hDen, hV, hQ0, hSurj,
      originalA, hOriginalA, hResidueIso, hDegree⟩ :=
    originalSameBasis_noSection_exists_fixedGraph_fullDegreeThreeCut_basisRepresentative_nonzero001
      p hp hp0 hno n y hpy j b a rho hRho v hv bad hBad
  let aCol := originalGrassmannChartLineColumn001 rho T 0
  let bCol := originalGrassmannChartLineColumn001 rho T 1
  let iPivot := originalGrassmannChartLinePivot001 rho 0
  let F := cubicLinePolynomial c aCol bCol
  let B := AdjoinRoot F
  let xB : Fin 4 → B := AdjoinRoot.root F • (fun l => algebraMap K B (aCol l)) +
    (fun l => algebraMap K B (bCol l))
  let ell : MvPolynomial (Fin 4) K := X j - C (aCol j) * X iPivot
  let I := equationIdeal p hp
  letI : Module.Finite K B := hBFinite
  letI : Field B := hField.toField
  let r : Spec (.of B) ⟶ hypersurface p hp := linearNormalizedPoint I xB ell hell hxell heI
  have hGraph : (finiteProductCoordinateEquiv (R := B) 2 2).symm
      (fun l => g (chartCoordinate I j l)) ∈
        grassmannianChartSubmodule B rho (T.map (algebraMap K B)) := by
    rw [show (fun l => g (chartCoordinate I j l)) = xB from funext hCoords]
    exact hxGraph
  obtain ⟨hFT, hEtale, points, hpJ, hAnchor, coefficients, hAux, hNonzero, hTangent⟩ :=
    cubicOriginalSelectedAuxiliary_sameJointGuard_exists_originalTangentSection001
      p hp n y hpy j b q hRep rankPivot pairPivot a i k H hRank rho T hField hRankB
      A v hPoints bad hKernel hTBad g hSurj hGraph
  exact ⟨q0, hq0, hqThrough, hqFresh, hqClass, T, hTBad, c, hc,
    hBFinite, hField, hell, hxell, heI, hxj, hxGraph, hClosed, hBase, hRankB,
    g, hCoords, hFactor, hDen, hV, hQ0, hSurj,
    originalA, hOriginalA, hResidueIso, hDegree,
    hFT, hEtale, points, hpJ, hAnchor, coefficients, hAux, hNonzero, hTangent⟩

end PfaffianDescent.Coray

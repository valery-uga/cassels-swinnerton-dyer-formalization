import Mathlib.Tactic.Trace
import PfaffianDescent.CorayOriginalLeastWindowPrincipalRankSmoothAssembly
import PfaffianDescent.CorayOriginalLeastWindowFinalCaseReduction
import PfaffianDescent.CorayOriginalFixedPrincipalNativePairBadLineGuard
import AllCharacteristics.ClosedPointAlgebra
import PfaffianDescent.CorayOriginalGrassmannGraphRankThreePoint

/-! Actual natural least-window tuple, extended by its own pair guards.
The inherited chart, residue point, full basis, anchor, principal h,
rank-pivot/index pair and SAME image factor f are all retained exactly. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped TensorProduct PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Natural ORIGINAL least-point data constructs its chart-free freedom
bound, one canonical principal rank/smooth tuple, then own pair equation,
own pair principal function, boundary product, whole-pair quotient and
nonzero original-K badline kernel polynomial. No desired field/rank/open,
freedom or pair/incidence outcome is an input, and no principal/chart/basis
is reselected between these actual constructions. The graph permutation
is constructed AFTER this SAME inherited j, with its second pivot equal
to j, and returned with its actual alignment proof; no rho input. -/
theorem coray_leastOriginalPoint_noSection_window_eq_four_or_ten_or_samePrincipal_pairBadLineGuard001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (n : ℕ)
    (hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    : let S := hypersurface p hp
    letI : IsIntegral S :=
      PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
    letI : Algebra K S.functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ((hypersurfaceToBase p hp).residueDegree P.1 = 4 ∧ n = 2) ∨
      ((hypersurfaceToBase p hp).residueDegree P.1 = 10 ∧ n = 3) ∨
      (3 ≤ n ∧ 7 ≤ (hypersurfaceToBase p hp).residueDegree P.1 ∧
      1 + 3 * n.choose 2 < (hypersurfaceToBase p hp).residueDegree P.1 ∧
      4 ≤ 3 * (n + 1).choose 2 - (hypersurfaceToBase p hp).residueDegree P.1 ∧
      (hypersurfaceToBase p hp).residueDegree P.1 + 5 ≤ (n + 3).choose 3 - n.choose 3 ∧
      ∃ (j : Fin 4)
        (gP : ChartRing (equationIdeal p hp) j →+* S.residueField P.1),
        gP.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K (S.residueField P.1) ∧
        Spec.map (CommRingCat.ofHom gP) ≫ chartι (equationIdeal p hp) j =
          S.fromSpecResidueField P.1 ∧
        ∃ (hpy : p.eval₂ (algebraMap K (S.residueField P.1))
            (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) = 0)
          (hChart : Nonempty (chartι (equationIdeal p hp) j).opensRange),
          letI := hChart
          ∃ (m : ℕ), 5 ≤ m ∧
            ∃ (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n
                (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy))
              (a : Fin m),
              let E := cubicThroughPointOriginalBasisRatioField p hp n
                (fun i => gP (chartCoordinate (equationIdeal p hp) j i)) hpy j b a
              let I := equationIdeal p hp
              let R := ChartRing I j
              let L := S.residueField P.1
              let y : Fin 4 → L := fun t => gP (chartCoordinate I j t)
              letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
              letI : Algebra K R := cubicChartNativeAlgebra p hp j
              letI : Module K R := Algebra.toModule
              let x := chartCoordinate I j
              let e := cubicThroughPointChartEvaluation p hp n
                (fun t => gP (chartCoordinate I j t)) hpy j
              let gradient : Fin 3 → R := fun t =>
                (pderiv (j.succAbove t) p).eval₂ (algebraMap K R) x
              let g := @affineChartGenericEvaluation R (inferInstance : CommRing R)
                S (inferInstance : IsIntegral S) (chartι I j) (isOpenImmersion_chartι I j)
                (inferInstance : Nonempty (chartι I j).opensRange)
              let xb : Fin m → R := fun t => cubicThroughPointChartEvaluation p hp n
                (fun i => gP (chartCoordinate I j i)) hpy j (b t)
              let B := Localization.Away (xb a)
              let u : Spec (.of B) ⟶ S :=
                Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι I j
              let C := cubicThroughPointBasisEvaluationImage p hp hp0 n
                (fun i => gP (chartCoordinate I j i)) hpy j b a
              Algebra.trdeg K E = 2 ∧
              ∃ pivot : Fin 3, ∃ h : R, ∃ i k : Fin m,
                g h ≠ 0 ∧
                originalNativeProjection_rankTwoOnPrincipalOpen p hp j pivot xb a i k h ∧
                Dense ((chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R))) ∧
                ∃ f : Spec (.of B) ⟶ C,
                  f ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n
                    (fun t => gP (chartCoordinate I j t)) hpy j b a =
                    nativeLocalizedProjectiveChartPoint (chartBaseMap I j) xb a ∧
                  f ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n
                    (fun t => gP (chartCoordinate I j t)) hpy j b a =
                    u ≫ hypersurfaceToBase p hp ∧
                  (chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) ⊆ Set.range u ∧
                  (∀ q : Spec (.of B),
                    u q ∈ (chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) →
                    f q ∈ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n
                      (fun t => gP (chartCoordinate I j t)) hpy j b a) ∧
              ∃ (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)),
                finSumFinEquiv (rho (Sum.inl (1 : Fin 2))) = j ∧
              ∃ (pairPivot : Fin 3) (d : R) (A : Fin m → R)
                (q : Fin m → MvPolynomial (Fin 4) K) (Ppair : MvPolynomial (Fin 4 ⊕ Fin 4) K) (kPair : Fin m),
                (∀ l, (q l).IsHomogeneous n ∧ (q l).eval₂ (algebraMap K L) y = 0 ∧
                  Ideal.Quotient.mk I.toIdeal (q l) = (b l).1.1 ∧
                  (q l).eval₂ (algebraMap K R) x = e (b l)) ∧
                gradient pairPivot ≠ 0 ∧
                let uPair := d * gradient pairPivot * A kPair
                let v := uPair * h
                g uPair ≠ 0 ∧ g h ≠ 0 ∧ g v ≠ 0 ∧
                originalNativeProjection_rankTwoOnPrincipalOpen p hp j pivot (fun l => e (b l)) a i k h ∧
                Dense ((chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R))) ∧
                (∀ (M : Type u) [Field M] [Algebra K M] (phi : R →ₐ[K] M), phi v ≠ 0 →
                  phi uPair ≠ 0 ∧ phi h ≠ 0 ∧ phi (gradient pairPivot) ≠ 0 ∧
                  (fun l => phi (A l)) ≠ 0 ∧
                  (∑ l, phi (A l) • (q l).eval₂ (algebraMap K (SurfacePlaneJet M))
                    (surfacePlaneJetCoordinates (fun l => phi (x l))
                      (fun r l => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
                        (fun s => phi (gradient s)) pairPivot l r))) = 0) ∧
                (f ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a =
                    nativeLocalizedProjectiveChartPoint (chartBaseMap I j) (fun l => e (b l)) a ∧
                  f ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
                    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e (b a))))) ≫ chartι I j) ≫
                      hypersurfaceToBase p hp ∧
                  (chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) ⊆
                    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e (b a))))) ≫ chartι I j) ∧
                  ∀ s : Spec (.of (Localization.Away (e (b a)))),
                    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (e (b a))))) ≫ chartι I j) s ∈
                      (chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) →
                    f s ∈ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a) ∧
                let T := R ⊗[K] R
                let Q : T := ∑ l, A l ⊗ₜ[K] e (b l)
                let F : T := Q * (v ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] v)
                Ppair.eval₂ (algebraMap K T)
                  (Sum.elim (fun l => x l ⊗ₜ[K] (1 : R)) (fun l => (1 : R) ⊗ₜ[K] x l)) = Q ∧
                Q ≠ 0 ∧ F ≠ 0 ∧ ringKrullDim (T ⧸ Ideal.span ({F} : Set T)) ≤ 3 ∧
                let B := T ⧸ Ideal.span ({F} : Set T)
                let xy := cubicOriginalWholePairChartAmbientVectors p hp j
                let xB := graphCoefficientMap (Ideal.Quotient.mk (Ideal.span ({F} : Set T))) xy.1
                let yB := graphCoefficientMap (Ideal.Quotient.mk (Ideal.span ({F} : Set T))) xy.2
                let D := originalPairGrassmannMinor rho xB yB
                let C := Localization.Away D
                let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho xB)
                let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho yB)
                let N := originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf D)
                ∃ bad : GrassmannianChartRing K 2 2, bad ≠ 0 ∧
                  (MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => N ij.1 ij.2)) bad = 0 ∧
                  closure (Set.range (originalPairMinorOpenToGrassmann (K := K) rho xB yB)) ≠
                    (Set.univ : Set (grassmannianScheme K 2 2))) := by
  classical
  trace "NATURAL_PAIR_ENTRY"
  have hNumericalData := coray_leastOriginalPoint_window_eq_four_or_ten_or_strict_integral_family001
    p hp hp0 P hPointCoprime hleast hno n hLower hUpper
  trace "NATURAL_PAIR_AFTER_CLEAN_NUMERICAL_HAVE"
  have hPrincipalData := coray_leastOriginalPoint_noSection_window_eq_four_or_ten_or_samePrincipal_rankTwo_smoothImage001
    p hp hp0 P hPointCoprime hleast hno n hLower hUpper
  trace "NATURAL_PAIR_AFTER_CLEAN_PRINCIPAL_HAVE"
  have hAligned := originalCubicChart_exists_graphPermutation_with_sameSecondPivot001
  trace "NATURAL_PAIR_AFTER_CLEAN_ALIGNMENT_PRODUCER"
  intro S
  letI : IsIntegral S :=
    PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
  letI : Algebra K S.functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  trace "NATURAL_PAIR_AFTER_ORIGINAL_INSTANCES"
  rcases hNumericalData with hFour | hTen | hNumerical
  · exact Or.inl hFour
  · exact Or.inr (Or.inl hTen)
  rcases hNumerical with ⟨hnThree, hPointLarge, hStrict, hFreedom, hSize, hAllIntegral, hMember⟩
  trace "NATURAL_PAIR_AFTER_NUMERICAL_OBTAIN"
  rcases hPrincipalData with hFour | hTen | hSurface
  · exact Or.inl hFour
  · exact Or.inr (Or.inl hTen)
  trace "NATURAL_PAIR_AFTER_PRINCIPAL_CASES"
  rcases hSurface with ⟨j, gP, hgBase, hgPoint, hpy, hChart, m, hFive, b, a,
    hE, pivot, h, i, k, hh, hRank, hDense, f, hFactor, hBase, hCover, hSmooth⟩
  trace "NATURAL_PAIR_AFTER_PRINCIPAL_OBTAIN"
  letI := hChart
  letI : Module.Finite K (S.residueField P.1) :=
    closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  have hSizeL : finrank K (S.residueField P.1) + 5 ≤ (n + 3).choose 3 - n.choose 3 := by
    rw [closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) P]
    exact hSize
  trace "NATURAL_PAIR_AFTER_RESIDUE_SIZE"
  have hRhoData := hAligned j
  trace "NATURAL_PAIR_AFTER_ALIGNMENT_APPLY"
  let rho : Equiv.Perm (Fin 2 ⊕ Fin 2) := Classical.choose hRhoData
  trace "NATURAL_PAIR_AFTER_RHO_CHOICE"
  have hPivot : originalGrassmannChartLinePivot001 rho 1 = j := Classical.choose_spec hRhoData
  trace "NATURAL_PAIR_AFTER_ALIGNED_RHO"
  have hPair := cubicThroughPointBasis_exists_pairBadLineGuard_for_sameActualPrincipalTuple001
    p hp hp0 n (fun t => gP (chartCoordinate (equationIdeal p hp) j t)) hpy j b a hSizeL rho
    pivot h i k f hh hRank hDense hFactor hBase hCover hSmooth
  trace "NATURAL_PAIR_AFTER_FIXED_H_HAVE"
  right
  right
  exact ⟨hnThree, hPointLarge, hStrict, hFreedom, hSize,
    j, gP, hgBase, hgPoint, hpy, hChart, m, hFive, b, a,
    hE, pivot, h, i, k, hh, hRank, hDense, f, hFactor, hBase, hCover, hSmooth, rho, hPivot, hPair⟩
  trace "NATURAL_PAIR_AFTER_FINAL_EXACT"

end PfaffianDescent.Coray
end

import PfaffianDescent.CorayOriginalLeastWindowSameRatioFieldTrdegTwo
import PfaffianDescent.CorayOriginalNativePrincipalRankSmoothGoodOpen

/-! Natural least-point window geometry on the SAME chosen original chart.
The exact original chart/residue point/full basis/anchor chosen by the natural
ratio-field endpoint is retained when constructing the original principal good
open and SAME image representative. No degree/rank/open outcome is an input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Natural ORIGINAL least-point, coprime-degree, no-section and least-window
hypotheses produce four/n2 or ten/n3, or ONE exact inherited canonical original
chart/residue point/full basis/anchor together with a constructed nonzero
original principal function, uniform native rank2 and genuine own pivot-gradient
nonvanishing, and SAME image factorization/ORIGINAL K square/smooth-above.
The SAME Etrdeg2 proof is constructed internally and retained in the output. -/
theorem coray_leastOriginalPoint_noSection_window_eq_four_or_ten_or_samePrincipal_rankTwo_smoothImage001
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
              let g := @affineChartGenericEvaluation R (inferInstance : CommRing R)
                S (inferInstance : IsIntegral S) (chartι I j) (isOpenImmersion_chartι I j)
                (inferInstance : Nonempty (chartι I j).opensRange)
              let x : Fin m → R := fun t => cubicThroughPointChartEvaluation p hp n
                (fun i => gP (chartCoordinate I j i)) hpy j (b t)
              let B := Localization.Away (x a)
              let u : Spec (.of B) ⟶ S :=
                Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι I j
              let C := cubicThroughPointBasisEvaluationImage p hp hp0 n
                (fun i => gP (chartCoordinate I j i)) hpy j b a
              Algebra.trdeg K E = 2 ∧
              ∃ pivot : Fin 3, ∃ h : R, ∃ i k : Fin m,
                g h ≠ 0 ∧
                originalNativeProjection_rankTwoOnPrincipalOpen p hp j pivot x a i k h ∧
                Dense ((chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R))) ∧
                ∃ f : Spec (.of B) ⟶ C,
                  f ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n
                    (fun t => gP (chartCoordinate I j t)) hpy j b a =
                    nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a ∧
                  f ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n
                    (fun t => gP (chartCoordinate I j t)) hpy j b a =
                    u ≫ hypersurfaceToBase p hp ∧
                  (chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) ⊆ Set.range u ∧
                  ∀ q : Spec (.of B),
                    u q ∈ (chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) →
                    f q ∈ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n
                      (fun t => gP (chartCoordinate I j t)) hpy j b a := by
  classical
  intro S
  letI : IsIntegral S :=
    PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
  letI : Algebra K S.functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  rcases coray_leastOriginalPoint_noSection_window_eq_four_or_ten_or_sameRatioField_trdeg_two001
      p hp hp0 P hPointCoprime hleast hno n hLower hUpper with hFour | hTen | hSurface
  · exact Or.inl hFour
  · exact Or.inr (Or.inl hTen)
  rcases hSurface with ⟨j, gP, hgBase, hgPoint, hpy, hChart, m, hFive, b, a, hE⟩
  letI := hChart
  obtain ⟨pivot, h, i, k, hh, hRank, hDense, f, hFactor, hBase, hCover, hSmooth⟩ :=
    cubicThroughPointBasis_exists_nonzeroOriginalPrincipal_rankTwo_sameImageSmooth_goodOpen001
      p hp hp0 n (fun t => gP (chartCoordinate (equationIdeal p hp) j t)) hpy j b a hE
  right
  right
  exact ⟨j, gP, hgBase, hgPoint, hpy, hChart, m, hFive, b, a,
    hE, pivot, h, i, k, hh, hRank, hDense, f, hFactor, hBase, hCover, hSmooth⟩

end PfaffianDescent.Coray
end

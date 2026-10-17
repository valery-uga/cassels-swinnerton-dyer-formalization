import PfaffianDescent.CorayOriginalNativePolynomialMinorSpecialization
import PfaffianDescent.CorayOriginalNativeMinorNumerator

/-! Natural ORIGINAL/SAME data constructs a dense original principal
open, and proves actual native rank2 there at every original coefficient
fieldpoint. No rank/open/numerator output is supplied as a premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TopologicalSpace TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME Etrdeg2 branch yields a genuine dense ORIGINAL principal
open and an actual nonzero2x2 normalized native projection fulljet minor
at every original chart fieldpoint on it, all for one constructed pivot
and one fixed pair of original basis indices. -/
theorem cubicThroughPointBasis_exists_denseOriginal_nativeRankTwo_principalOpen001
    {K L : Type u} [Field K] [CharZero K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m) :
    let I := equationIdeal p hp
    let R := ChartRing I j
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let g := @affineChartGenericEvaluation R (inferInstance : CommRing R)
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι I j) (isOpenImmersion_chartι I j)
      (inferInstance : Nonempty (chartι I j).opensRange)
    let x : Fin m → R := fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)
    let grad : Fin 3 → R := fun t =>
      (pderiv (j.succAbove t) p).eval₂ (chartBaseMap I j) (chartCoordinate I j)
    Algebra.trdeg K (cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a) = 2 →
    ∃ pivot : Fin 3, ∃ q : Fin m → MvPolynomial (Fin 4) K,
      (∀ t, (q t).eval₂ (chartBaseMap I j) (chartCoordinate I j) = x t) ∧
      let N : Fin m → Fin 2 → R := fun t r =>
        grad pivot * (pderiv (j.succAbove (pivot.succAbove r)) (q t)).eval₂
          (chartBaseMap I j) (chartCoordinate I j) -
        grad (pivot.succAbove r) * (pderiv (j.succAbove pivot) (q t)).eval₂
          (chartBaseMap I j) (chartCoordinate I j)
      ∃ i k : Fin m,
      let D := normalizedProjectionMinorNumerator (x i) (x k) (x a) (N i) (N k) (N a)
      let H := grad pivot * x a * D
      g H ≠ 0 ∧
      Dense ((chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R))) ∧
      ∀ (M : Type u) [Field M] [Algebra K M] (h : R →+* M),
        h.comp (chartBaseMap I j) = algebraMap K M → h H ≠ 0 →
        let z : Fin 4 → M := fun t => h (chartCoordinate I j t)
        let v : Fin 2 → Fin 4 → M := fun r t =>
          PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            (fun s => aeval z (pderiv (j.succAbove s) (p.map (algebraMap K M)))) pivot t r
        (pderiv (j.succAbove pivot) p).eval₂ (algebraMap K M) z ≠ 0 ∧
        ∃ hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0,
        ∃ hAnchor : surfacePlaneJetCoordinates z v j = 1,
        let J := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
        ∃ hUnit : IsUnit (J (x a)),
        let mu : Localization.Away (x a) →+* SurfacePlaneJet M := IsLocalization.Away.lift (x a) hUnit
        let row : Fin m → Fin 2 → M := fun t =>
          (mu (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a
            (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a t))).snd
        row i 0 * row k 1 - row i 1 * row k 0 ≠ 0 := by
  let I := equationIdeal p hp
  let R := ChartRing I j
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let g := @affineChartGenericEvaluation R (inferInstance : CommRing R)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstance : Nonempty (chartι I j).opensRange)
  let x : Fin m → R := fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)
  change Algebra.trdeg K (cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a) = 2 → _
  intro hE
  obtain ⟨pivot, hG, q, hrep, i, k, hD, hH, hOpen, hDense⟩ :=
    cubicThroughPointBasis_exists_originalNativeMinorNumerator_densePrincipalOpen001
      p hp hp0 n y hpy j b a hE
  refine ⟨pivot, q, hrep, i, k, hH, hDense, ?_⟩
  intro M iField iAlgebra h hBase hNonzero
  exact cubicChartPolynomialFamily_nativeNormalizedMinor_of_originalNumerator_nonzero001
    p hp j pivot x q hrep a i k h hBase hNonzero

end PfaffianDescent.Coray
end

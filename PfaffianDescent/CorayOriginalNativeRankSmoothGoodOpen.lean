import Mathlib.Tactic.Trace
import PfaffianDescent.CorayOriginalNativeDenseRankOpen
import PfaffianDescent.CorayOriginalNativeSameImageSmoothOpen

/-! SAME original projection: a genuine dense original open with actual
native rank two at every chart fieldpoint and image in the SAME smooth
locus over ORIGINAL K. No desired rank/open outcome supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TopologicalSpace TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An explicit statement of uniform rank2 for the literal normalized
native projection chart on an original principal open. This predicate
records the actual cubic fulljet, original coefficient square, fulljet
denominator unit and exact normalized native target-coordinate minor.
It retains the actually nonzero original pivot gradient, so genuine
independently constructed pivot frames can be compared. -/
def originalNativeProjection_rankTwoOnPrincipalOpen
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) (pivot : Fin 3)
    {m : ℕ} (x : Fin m → ChartRing (equationIdeal p hp) j) (a i k : Fin m)
    (H : ChartRing (equationIdeal p hp) j) : Prop :=
  ∀ (M : Type u) [Field M] [Algebra K M]
    (h : ChartRing (equationIdeal p hp) j →+* M),
    h.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M → h H ≠ 0 →
    let z : Fin 4 → M := fun t => h (chartCoordinate (equationIdeal p hp) j t)
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
      (mu (nativeLocalizedProjectiveChartMap (chartBaseMap (equationIdeal p hp) j) x a
        (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a t))).snd
    row i 0 * row k 1 - row i 1 * row k 0 ≠ 0

/-- Bounded construction phase: accepted actual dense tuple is converted
into the exact uniform rank abbreviation and dense original principal
image in its own ordinary declaration. No desired H/rank/density tuple
is supplied; the SAME Etrdeg2 branch internally constructs all of it. -/
private theorem cubicThroughPointBasis_exists_dense_rankPredicate_phase001
    {K L : Type u} [Field K] [CharZero K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    let R := ChartRing I j
    let F := S.functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let x : Fin m → R := fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)
    Algebra.trdeg K (cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a) = 2 →
    ∃ pivot : Fin 3, ∃ H : R, ∃ i k : Fin m,
      originalNativeProjection_rankTwoOnPrincipalOpen p hp j pivot x a i k H ∧
      Dense ((chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R))) := by
  let S := hypersurface p hp
  let I := equationIdeal p hp
  let R := ChartRing I j
  let F := S.functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let x : Fin m → R := fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)
  let grad : Fin 3 → R := fun t =>
    (pderiv (j.succAbove t) p).eval₂ (chartBaseMap I j) (chartCoordinate I j)
  change Algebra.trdeg K (cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a) = 2 → _
  intro hE
  obtain ⟨pivot, q, hrep, i, k, hH, hRankDense, hRank⟩ :=
    cubicThroughPointBasis_exists_denseOriginal_nativeRankTwo_principalOpen001 p hp hp0 n y hpy j b a hE
  let N : Fin m → Fin 2 → R := fun t r =>
    grad pivot * (pderiv (j.succAbove (pivot.succAbove r)) (q t)).eval₂
      (chartBaseMap I j) (chartCoordinate I j) -
    grad (pivot.succAbove r) * (pderiv (j.succAbove pivot) (q t)).eval₂
      (chartBaseMap I j) (chartCoordinate I j)
  let D := normalizedProjectionMinorNumerator (x i) (x k) (x a) (N i) (N k) (N a)
  let H := grad pivot * x a * D
  have hActualRank : originalNativeProjection_rankTwoOnPrincipalOpen p hp j pivot x a i k H := hRank
  exact ⟨pivot, H, i, k, hActualRank, hRankDense⟩

/-- Ordinary default200000 intersection diagnostic/cut: from the actual
constructed dense principal H, internally construct the SAME smooth-target
representative and dense original intersection. No f/smooth/open conclusion
is supplied. Natural final producer gets H/density from actual phase1. -/
private theorem cubicThroughPointBasis_fixedDensePrincipal_exists_sameImageSmoothIntersection_phase001
    {K L : Type u} [Field K] [CharZero K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m)
    (H : ChartRing (equationIdeal p hp) j)
    (hRankDense : Dense ((chartι (equationIdeal p hp) j) ''
      (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum (ChartRing (equationIdeal p hp) j))))) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    let R := ChartRing I j
    let x : Fin m → R := fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)
    let B := Localization.Away (x a)
    let u : Spec (.of B) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι I j
    let C := cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a

    ∃ f : Spec (.of B) ⟶ C,
        f ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a =
          nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a ∧
        f ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
          u ≫ hypersurfaceToBase p hp ∧
        ∃ U : TopologicalSpace.Opens S,
          Dense (U : Set S) ∧
          (U : Set S) ⊆ (chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R)) ∧
          (U : Set S) ⊆ Set.range u ∧
          ∀ q : Spec (.of B), u q ∈ U →
            f q ∈ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a := by
  let S := hypersurface p hp
  let I := equationIdeal p hp
  let R := ChartRing I j
  let x : Fin m → R := fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)
  let B := Localization.Away (x a)
  let u : Spec (.of B) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι I j
  obtain ⟨f, hFactor, hBase, W, hW_eq, hWDense, V, hVImage, hVDense, hWSmooth⟩ :=
    cubicThroughPointBasis_nativeDenominatorOpen_exists_denseOriginalImageSmoothOpen001 p hp hp0 n y hpy j b a
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of R) (x a)
  letI : IsOpenImmersion (chartι I j) := isOpenImmersion_chartι I j
  letI : IsOpenImmersion u :=
    IsOpenImmersion.comp (Spec.map (CommRingCat.ofHom (algebraMap R B))) (chartι I j)
  let VRank : TopologicalSpace.Opens S :=
    ⟨(chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R)),
      (chartι I j).isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen H).isOpen⟩
  have hVRankDense : Dense (VRank : Set S) := hRankDense
  let U : TopologicalSpace.Opens S := V ⊓ VRank
  have hUDense : Dense (U : Set S) := hVDense.inter_of_isOpen_left hVRankDense V.isOpen
  refine ⟨f, hFactor, hBase, U, hUDense, ?_, ?_, ?_⟩
  · intro t ht
    exact ht.2
  · intro t ht
    have hImage : t ∈ u '' (W : Set (Spec (.of B))) := by
      rw [← hVImage]
      exact ht.1
    obtain ⟨q', hq', hq't⟩ := hImage
    exact ⟨q', hq't⟩
  · intro q' hq'
    have hImage : u q' ∈ u '' (W : Set (Spec (.of B))) := by
      rw [← hVImage]
      exact hq'.1
    obtain ⟨t, ht, htq⟩ := hImage
    have hEq : t = q' := u.isOpenEmbedding.injective htq
    subst t
    exact hWSmooth q' ht


/-- Natural original data in the SAME Etrdeg2 branch constructs one
actual dense ORIGINAL good open inside the fixed native denominator
representative. Uniform actual normalized native rank2 and smooth SAME
image membership both hold there, retaining the exact original K square. -/
theorem cubicThroughPointBasis_exists_denseOriginal_nativeRankTwo_sameImageSmooth_goodOpen001
    {K L : Type u} [Field K] [CharZero K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    let R := ChartRing I j
    let x : Fin m → R := fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)
    let B := Localization.Away (x a)
    let u : Spec (.of B) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι I j
    let C := cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a
    let F := S.functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    Algebra.trdeg K (cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a) = 2 →
    ∃ pivot : Fin 3, ∃ H : R, ∃ i k : Fin m,
      originalNativeProjection_rankTwoOnPrincipalOpen p hp j pivot x a i k H ∧
      ∃ f : Spec (.of B) ⟶ C,
        f ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a =
          nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a ∧
        f ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
          u ≫ hypersurfaceToBase p hp ∧
        ∃ U : TopologicalSpace.Opens S,
          Dense (U : Set S) ∧
          (U : Set S) ⊆ (chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R)) ∧
          (U : Set S) ⊆ Set.range u ∧
          ∀ q : Spec (.of B), u q ∈ U →
            f q ∈ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a := by
  trace "RANKSMOOTH_BINDER_ENTRY"
  intro S I R x B u C F hE
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  trace "RANKSMOOTH_BINDER_AFTER_INTRO"
  obtain ⟨pivot, H, i, k, hActualRank, hRankDense⟩ :=
    cubicThroughPointBasis_exists_dense_rankPredicate_phase001 p hp hp0 n y hpy j b a hE
  trace "RANKSMOOTH_BINDER_AFTER_PHASE1"
  refine ⟨pivot, H, i, k, hActualRank, ?_⟩
  trace "RANKSMOOTH_BINDER_AFTER_TUPLE_HEAD"
  have hTail := cubicThroughPointBasis_fixedDensePrincipal_exists_sameImageSmoothIntersection_phase001
    p hp hp0 n y hpy j b a H hRankDense
  trace "RANKSMOOTH_BINDER_AFTER_PHASE2"
  exact hTail
  trace "RANKSMOOTH_BINDER_AFTER_EXACT"

end PfaffianDescent.Coray
end

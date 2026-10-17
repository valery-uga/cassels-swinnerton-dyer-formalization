import Mathlib.Tactic.Trace
import PfaffianDescent.CorayOriginalNativeRankSmoothGoodOpen

/-! Refine the genuinely constructed ORIGINAL rank/smooth good open by
one literal original nonzero basic-open function, for actual pair-boundary
composition. No good open or rank output is supplied at the natural root. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TopologicalSpace TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A genuinely dense original open admits a nonzero original chart
basic-open refinement at the actual generic point. -/
theorem denseOriginalOpen_exists_chartBasicRefinement001
    {R F : Type u} [CommRing R] [Field F] {X : Scheme.{u}} [IsIntegral X]
    (g : R →+* F) (hg : Function.Injective g)
    (i : Spec (.of R) ⟶ X) [IsOpenImmersion i]
    (U : TopologicalSpace.Opens X) (hU : Dense (U : Set X)) :
    ∃ h : R, g h ≠ 0 ∧
      (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) ⊆ (i ⁻¹ᵁ U : Set (Spec (.of R))) ∧
      i '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) ⊆ (U : Set X) ∧
      Dense (i '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R))) := by
  letI : IsDomain R := hg.isDomain g
  letI : IsIntegral (Spec (.of R)) := inferInstance
  have hGenericU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU.nonempty)
  have hPullback : genericPoint (Spec (.of R)) ∈ i ⁻¹ᵁ U := by
    change i (genericPoint (Spec (.of R))) ∈ U
    rw [genericPoint_eq_of_isOpenImmersion i]
    exact hGenericU
  obtain ⟨V, ⟨h, rfl⟩, hGenericBasic, hSubset⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      hPullback (i ⁻¹ᵁ U).isOpen
  have hNonzero : h ≠ 0 := by
    change genericPoint (Spec (.of R)) ∈ PrimeSpectrum.basicOpen h at hGenericBasic
    rw [genericPoint_eq_bot_of_affine (.of R)] at hGenericBasic
    have hNotMem : h ∉ (⊥ : PrimeSpectrum R).asIdeal :=
      (PrimeSpectrum.mem_basicOpen h (⊥ : PrimeSpectrum R)).mp hGenericBasic
    simpa only [PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] using hNotMem
  have hImageSubset : i '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) ⊆ (U : Set X) := by
    rintro _ ⟨q, hq, rfl⟩
    exact hSubset hq
  have hDense : Dense (i '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R))) :=
    (i.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen h).isOpen).dense
      ⟨i (genericPoint (Spec (.of R))), genericPoint (Spec (.of R)), hGenericBasic, rfl⟩
  refine ⟨h, ?_, hSubset, hImageSubset, hDense⟩
  intro hzero
  apply hNonzero
  exact hg (hzero.trans (map_zero g).symm)

/-- Literal basic-open containment preserves nonvanishing under every
actual fieldpoint ring map. No residue field or point condition is lost. -/
theorem basicOpen_subset_fieldMap_ne_zero001
    {R M : Type u} [CommRing R] [Field M] (h H : R)
    (hSubset : (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.basicOpen H)
    (g : R →+* M) (hh : g h ≠ 0) : g H ≠ 0 := by
  have hPoint : PrimeSpectrum.comap g (⊥ : PrimeSpectrum M) ∈ PrimeSpectrum.basicOpen h := by
    simpa only [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal,
      Ideal.mem_comap, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] using hh
  have hH := hSubset hPoint
  change PrimeSpectrum.comap g (⊥ : PrimeSpectrum M) ∈ PrimeSpectrum.basicOpen H at hH
  have hNotMem : H ∉ (PrimeSpectrum.comap g (⊥ : PrimeSpectrum M)).asIdeal :=
    (PrimeSpectrum.mem_basicOpen H (PrimeSpectrum.comap g (⊥ : PrimeSpectrum M))).mp hH
  simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] using hNotMem

/-- The exact uniform native rank predicate restricts along literal
original basic-open containment, using actual fieldpoint nonvanishing. -/
theorem originalNativeProjection_rankTwoOnPrincipalOpen_mono_basicOpen001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) (pivot : Fin 3)
    {m : ℕ} (x : Fin m → ChartRing (equationIdeal p hp) j) (a i k : Fin m)
    (h H : ChartRing (equationIdeal p hp) j)
    (hSubset : (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum (ChartRing (equationIdeal p hp) j))) ⊆
      PrimeSpectrum.basicOpen H)
    (hRank : originalNativeProjection_rankTwoOnPrincipalOpen p hp j pivot x a i k H) :
    originalNativeProjection_rankTwoOnPrincipalOpen p hp j pivot x a i k h := by
  unfold originalNativeProjection_rankTwoOnPrincipalOpen
  intro M iField iAlgebra g hBase hNonzero
  exact hRank M g hBase (basicOpen_subset_fieldMap_ne_zero001 h H hSubset g hNonzero)

/-- Natural SAME Etrdeg2 data constructs ONE literal original nonzero
basic-open function controlling both actual native rank2 and smooth
SAME image membership. Exact original native map and original K square
are retained. This function can be multiplied by the own-pair pivot or
other original boundary equations without changing the chart or map. -/
theorem cubicThroughPointBasis_exists_nonzeroOriginalPrincipal_rankTwo_sameImageSmooth_goodOpen001
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
    let g := @affineChartGenericEvaluation R (inferInstance : CommRing R)
      S (inferInstance : IsIntegral S) (chartι I j) (isOpenImmersion_chartι I j)
      (inferInstance : Nonempty (chartι I j).opensRange)
    let x : Fin m → R := fun t => cubicThroughPointChartEvaluation p hp n y hpy j (b t)
    let B := Localization.Away (x a)
    let u : Spec (.of B) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ chartι I j
    let C := cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a
    Algebra.trdeg K (cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a) = 2 →
    ∃ pivot : Fin 3, ∃ h : R, ∃ i k : Fin m,
      g h ≠ 0 ∧ originalNativeProjection_rankTwoOnPrincipalOpen p hp j pivot x a i k h ∧
      Dense ((chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R))) ∧
      ∃ f : Spec (.of B) ⟶ C,
        f ≫ cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a =
          nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a ∧
        f ≫ cubicThroughPointBasisEvaluationImageToBase p hp hp0 n y hpy j b a =
          u ≫ hypersurfaceToBase p hp ∧
        (chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) ⊆ Set.range u ∧
        ∀ q : Spec (.of B),
          u q ∈ (chartι I j) '' (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) →
          f q ∈ cubicThroughPointBasisEvaluationImageSmoothOpen p hp hp0 n y hpy j b a := by
  trace "PRINCIPAL_PUBLIC_ENTRY"
  intro S I R F g x B u C hE
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  trace "PRINCIPAL_PUBLIC_AFTER_INTRO"
  obtain ⟨pivot, H, i, k, hRank, f, hFactor, hBase, U, hUDense, hUSubset, hUCover, hUSmooth⟩ :=
    cubicThroughPointBasis_exists_denseOriginal_nativeRankTwo_sameImageSmooth_goodOpen001 p hp hp0 n y hpy j b a hE
  trace "PRINCIPAL_PUBLIC_AFTER_RANKSMOOTH"
  have hg : Function.Injective g := @affineChartGenericEvaluation_injective R (inferInstance : CommRing R)
    S (inferInstance : IsIntegral S) (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstance : Nonempty (chartι I j).opensRange)
  trace "PRINCIPAL_PUBLIC_AFTER_GENERIC_INJECTIVE"
  letI : IsOpenImmersion (chartι I j) := isOpenImmersion_chartι I j
  letI : IsIntegral (scheme I) := by
    change IsIntegral (hypersurface p hp)
    infer_instance
  trace "PRINCIPAL_PUBLIC_AFTER_CHART_TARGET_INTEGRAL"
  obtain ⟨h, hh, hPullback, hImageSubset, hDense⟩ :=
    denseOriginalOpen_exists_chartBasicRefinement001 g hg (chartι I j) U hUDense
  trace "PRINCIPAL_PUBLIC_AFTER_BASIC_REFINEMENT"
  have hSmallSubset : (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.basicOpen H := by
    intro q hq
    have hImage : (chartι I j) q ∈ (chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R)) :=
      hUSubset (hImageSubset ⟨q, hq, rfl⟩)
    exact (chartι I j).isOpenEmbedding.injective.mem_set_image.mp hImage
  have hSmallRank := originalNativeProjection_rankTwoOnPrincipalOpen_mono_basicOpen001
    p hp j pivot x a i k h H hSmallSubset hRank
  trace "PRINCIPAL_PUBLIC_AFTER_RANK_RESTRICTION"
  refine ⟨pivot, h, i, k, hh, hSmallRank, hDense, f, hFactor, hBase, ?_, ?_⟩
  · exact hImageSubset.trans hUCover
  · intro q hq
    exact hUSmooth q (hImageSubset hq)

end PfaffianDescent.Coray
end

import PfaffianDescent.CorayAiNativeBasisDenominator
import PfaffianDescent.CorayNativeLocalizedProjectiveHyperplanePullback
import PfaffianDescent.CorayEntireModelIncidenceCycle
import AllCharacteristics.ClosedPointAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Proper

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original auxiliary point internally chooses a native basis chart,
then maps through THAT localization into the original projective evaluation
space. Its image is a genuine closed point; its ORIGINAL degree divides the
auxiliary degree. The whole hyperplane value criterion is literal, not a
geometric-image or transitivity premise. -/
theorem originalAuxiliaryPoint_nonzeroPolynomial_exists_nativeBasisChart_closedImage001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (q0 : MvPolynomial (Fin 4) K) (hq0 : q0.IsHomogeneous n)
    (hqP : q0.eval₂ (algebraMap K L) y = 0)
    (A : closedPoints (hypersurface p hp)) :
    let S := hypersurface p hp
    let I := equationIdeal p hp
    let R := ChartRing I j
    let M := S.residueField A.1
    letI := pointAlgebra (hypersurfaceToBase p hp) A.1
    ∀ gA : R →+* M,
      gA.comp (chartBaseMap I j) = algebraMap K M →
      Spec.map (CommRingCat.ofHom gA) ≫ chartι I j = S.fromSpecResidueField A.1 →
      gA (q0.eval₂ (chartBaseMap I j) (chartCoordinate I j)) ≠ 0 →
      let e := cubicThroughPointChartEvaluation p hp n y hpy j
      let x := fun i => e (b i)
      ∃ (a : Fin m) (ha : gA (x a) ≠ 0),
        let ell : Localization.Away (x a) →+* M :=
          IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr ha)
        let gamma := Spec.map (CommRingCat.ofHom ell)
        let u := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (x a)))) ≫ chartι I j
        let rho := gamma ≫ nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a
        ∃ T : closedPoints (scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))),
          T.1 = rho (IsLocalRing.closedPoint M) ∧
          gamma ≫ u = S.fromSpecResidueField A.1 ∧
          rho ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) =
            Spec.map (CommRingCat.ofHom (algebraMap K M)) ∧
          (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))).residueDegree T.1 ∣
            (hypersurfaceToBase p hp).residueDegree A.1 ∧
          ∀ c : Fin m → K,
            ell (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a
              (projectiveChartLinearForm a c)) = 0 ↔ gA (e (∑ i, c i • b i)) = 0 := by
  classical
  intro S I R M
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  intro gA hgBase hgPoint hqA
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let x := fun i => e (b i)
  obtain ⟨a, ha⟩ := cubicThroughPointBasis_nonzero_polynomial_value_exists_nativeDenominator001
    p hp n y hpy j b q0 hq0 hqP gA hqA
  refine ⟨a, ha, ?_⟩
  let ell : Localization.Away (x a) →+* M :=
    IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr ha)
  let gamma := Spec.map (CommRingCat.ofHom ell)
  let u := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (x a)))) ≫ chartι I j
  let rho := gamma ≫ nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a
  let J : HomogeneousIdeal (homogeneousSubmodule (Fin m) K) := ⊥
  let pi := toBase J
  have hEll : ell.comp (algebraMap R (Localization.Away (x a))) = gA :=
    IsLocalization.Away.lift_comp _ _
  have hSpec : gamma ≫ Spec.map
      (CommRingCat.ofHom (algebraMap R (Localization.Away (x a)))) =
      Spec.map (CommRingCat.ofHom gA) := by
    dsimp only [gamma]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    exact congrArg CommRingCat.ofHom hEll
  have hSource : gamma ≫ u = S.fromSpecResidueField A.1 := by
    dsimp only [u]
    rw [← Category.assoc, hSpec]
    exact hgPoint
  have hBase : rho ≫ pi = Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
    dsimp only [rho, pi, J]
    rw [Category.assoc, nativeLocalizedProjectiveChartPoint_toBase001, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    exact (RingHom.congr_fun hEll (chartBaseMap I j t)).trans (RingHom.congr_fun hgBase t)
  letI : Module.Finite K M := closedPoint_moduleFinite (hypersurfaceToBase p hp) A
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K M))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsProper (rho ≫ pi) := by rw [hBase]; infer_instance
  letI : IsProper rho := IsProper.of_comp rho pi
  let T : closedPoints (scheme J) := ⟨rho (IsLocalRing.closedPoint M), by
    change IsClosed ({rho (IsLocalRing.closedPoint M)} : Set (scheme J))
    rw [← Set.image_singleton]
    exact rho.isClosedMap _ isClosed_singleton⟩
  have hDegree : pi.residueDegree T.1 ∣ (hypersurfaceToBase p hp).residueDegree A.1 := by
    have h := residueDegree_comp rho pi (IsLocalRing.closedPoint M)
    rw [hBase, modelFieldSpectrum_original_residueDegree_eq_finrank,
      closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) A] at h
    exact ⟨rho.residueDegree (IsLocalRing.closedPoint M), h⟩
  refine ⟨T, rfl, hSource, hBase, hDegree, ?_⟩
  intro c
  have hNumerator : (∑ i, chartBaseMap I j (c i) * x i) = e (∑ i, c i • b i) := by
    have hSum : e (∑ i, c i • b i) = ∑ i, c i • e (b i) := by simp only [map_sum, map_smul]
    rw [hSum]
    apply Finset.sum_congr rfl
    intro i _
    exact (gradedChartNative_smul_eq_baseMap_mul (grading I) (c i) (e (b i))).symm
  have hKernel := (nativeLocalizedProjectiveChartMap_hyperplane_pullback001
    (chartBaseMap I j) x a).2.2.2 c (RingHom.ker ell)
  change ell (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a
      (projectiveChartLinearForm a c)) = 0 ↔
    ell (algebraMap R (Localization.Away (x a)) (∑ i, chartBaseMap I j (c i) * x i)) = 0 at hKernel
  have hValue : ell (algebraMap R (Localization.Away (x a))
      (e (∑ i, c i • b i))) = gA (e (∑ i, c i • b i)) :=
    RingHom.congr_fun hEll (e (∑ i, c i • b i))
  rw [hNumerator, hValue] at hKernel
  exact hKernel

end PfaffianDescent.Coray

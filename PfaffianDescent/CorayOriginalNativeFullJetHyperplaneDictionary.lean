import PfaffianDescent.CorayBoundedOriginalTangentIncidence
import PfaffianDescent.CorayBoundedOriginalChartEvaluation
import PfaffianDescent.CorayOriginalChartGenericLinearity
import PfaffianDescent.CorayNativeLocalizedProjectiveHyperplanePullback
import AllCharacteristics.HomogeneousChartEvaluation
import PfaffianDescent.CubicNormalizedSurfaceTangentJets
import AllCharacteristics.ProjectiveFiberSmoothness

/-! Literal original full-jet evaluation on the native basis projection chart.
This constructs a map and proves its full-jet hyperplane criterion. It does
not presume or assert the separate joint tangent-good auxiliary selection. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Original cubic smoothness constructs a native full jet at the actual
original-K chart field point. No pivot, tangent frame or jet is supplied. -/
theorem smoothOriginalCubic_chartFieldPoint_exists_nativeFullJet001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M) :
    let z : Fin 4 → M := fun i => g (chartCoordinate (equationIdeal p hp) j i)
    p.eval₂ (algebraMap K M) z = 0 ∧
    ∃ pivot : Fin 3,
      (pderiv (j.succAbove pivot) p).eval₂ (algebraMap K M) z ≠ 0 ∧
      let v : Fin 2 → Fin 4 → M := fun r i =>
        PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
          (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K M)))) pivot i r
      p.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v) = 0 ∧
      surfacePlaneJetCoordinates z v j = 1 := by
  let I := equationIdeal p hp
  let z : Fin 4 → M := fun i => g (chartCoordinate I j i)
  have hz : z j = 1 := by
    change g (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  have hpI : p ∈ I.toIdeal := Ideal.subset_span (Set.mem_singleton p)
  have hpz : p.eval₂ (algebraMap K M) z = 0 := by
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p hpI)
    rw [hom_eval₂, hBase, map_zero] at h
    exact h
  let f := algebraMap K M
  have hpM0 : p.map f ≠ 0 := by
    intro h
    apply hp0
    apply MvPolynomial.map_injective f f.injective
    simpa using h
  letI : Smooth (hypersurfaceToBase (p.map f) (hp.map f)) :=
    smooth_hypersurfaceToBase_map f p hp
  have hpMz : aeval z (p.map f) = 0 := by
    simpa only [aeval_eq_eval, MvPolynomial.eval_map] using hpz
  obtain ⟨pivot, hpivotM⟩ := PfaffianDescent.cubicNormalizedSurfacePoint_exists_nonzero_gradient
    (p.map f) (hp.map f) hpM0 j z hz hpMz
  have hpivot : (pderiv (j.succAbove pivot) p).eval₂ f z ≠ 0 := by
    simpa only [aeval_eq_eval, MvPolynomial.pderiv_map, MvPolynomial.eval_map] using hpivotM
  let v : Fin 2 → Fin 4 → M := fun r i =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun t => aeval z (pderiv (j.succAbove t) (p.map f))) pivot i r
  have hCoordinates : surfacePlaneJetCoordinates z v =
      (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet (p.map f) j z pivot :
        Fin 4 → SurfacePlaneJet M) := rfl
  have hCoeff : (algebraMap M (SurfacePlaneJet M)).comp f =
      algebraMap K (SurfacePlaneJet M) :=
    (IsScalarTower.algebraMap_eq K M (SurfacePlaneJet M)).symm
  have hpJet : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0 := by
    rw [hCoordinates]
    have h := PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet_cubic
      (p.map f) j z pivot hpMz hpivotM
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at h
    change p.eval₂ ((algebraMap M (SurfacePlaneJet M)).comp f)
      (PfaffianDescent.cubicNormalizedSurfacePoint_tangentJet (p.map f) j z pivot) = 0 at h
    rw [hCoeff] at h
    exact h
  have hAnchor : surfacePlaneJetCoordinates z v j = 1 := by
    have hRow : (fun r => v r j) = 0 := by
      funext r
      exact congrFun (PfaffianDescent.cubicClosedPointSerreSurfaceJets_row_diag j
        (fun t => aeval z (pderiv (j.succAbove t) (p.map f))) pivot) r
    change (inl (z j) + inr (fun r => v r j) : SurfacePlaneJet M) = 1
    rw [hz, hRow]
    simp only [TrivSqZeroExt.inr_zero, add_zero, TrivSqZeroExt.inl_one]
  exact ⟨hpz, pivot, hpivot, hpJet, hAnchor⟩

/-- The actual normalized surface full jet constructs an original chart map. -/
def cubicNormalizedFullJetChartMap
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (j : Fin 4) (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0)
    (hAnchor : surfacePlaneJetCoordinates z v j = 1) :
    ChartRing (equationIdeal p hp) j →+* SurfacePlaneJet M :=
  AllCharacteristics.GradedChart.liftCoordinateOne
    (grading (equationIdeal p hp)) (coordinate (equationIdeal p hp) j)
    (cubicCoordinateAlgebraEvaluation p hp (surfacePlaneJetCoordinates z v) hpJ).toRingHom
    (by
      change MvPolynomial.eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates z v) (X j) = 1
      simpa only [eval₂_X] using hAnchor)

/-- Its coefficients are the ORIGINAL K coefficients in the whole jet. -/
theorem cubicNormalizedFullJetChartMap_base001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (j : Fin 4) (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0)
    (hAnchor : surfacePlaneJetCoordinates z v j = 1) (t : K) :
    cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
      (chartBaseMap (equationIdeal p hp) j t) = algebraMap K (SurfacePlaneJet M) t := by
  let I := equationIdeal p hp
  let qEval : CoordinateRing I →+* SurfacePlaneJet M :=
    (cubicCoordinateAlgebraEvaluation p hp (surfacePlaneJetCoordinates z v) hpJ).toRingHom
  have hOne : qEval (coordinate I j) = 1 := by
    change MvPolynomial.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) (X j) = 1
    simpa only [eval₂_X] using hAnchor
  change (AllCharacteristics.GradedChart.liftCoordinateOne (grading I) (coordinate I j) qEval hOne)
    (AllCharacteristics.GradedChart.baseMap (grading I) (z := coordinate I j) t) = _
  rw [AllCharacteristics.GradedChart.liftCoordinateOne_baseMap]
  exact (cubicCoordinateAlgebraEvaluation p hp (surfacePlaneJetCoordinates z v) hpJ).commutes t

/-- The original chart map sends degree-n fractions to their entire jet value. -/
theorem cubicNormalizedFullJetChartMap_section001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0)
    (hAnchor : surfacePlaneJetCoordinates z v j = 1)
    (s : cubicThroughCoordinateSections p hp n y hpy) :
    cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j s) =
      cubicGradeCoordinateEvaluation p hp n (surfacePlaneJetCoordinates z v) hpJ s.1 := by
  exact AllCharacteristics.GradedChart.liftCoordinateOne_mk
    (grading (equationIdeal p hp)) (coordinate (equationIdeal p hp) j)
    (cubicCoordinateAlgebraEvaluation p hp (surfacePlaneJetCoordinates z v) hpJ).toRingHom
    (by
      change MvPolynomial.eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates z v) (X j) = 1
      simpa only [eval₂_X] using hAnchor)
    (coordinate_mem (equationIdeal p hp) j) n s.1.1
    (by simpa only [smul_eq_mul, mul_one] using s.1.2)

/-- Whole jet residue value is the same original ordinary evaluation. -/
theorem cubicGradeSurfaceJet_fst001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (z : Fin 4 → M) (hpz : p.eval₂ (algebraMap K M) z = 0)
    (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0)
    (s : grading (equationIdeal p hp) n) :
    (cubicGradeCoordinateEvaluation p hp n (surfacePlaneJetCoordinates z v) hpJ s).fst =
      cubicGradeCoordinateEvaluation p hp n z hpz s := by
  obtain ⟨q, _hq, hqs⟩ := cubicGradeSection_exists_polynomial_representative p hp n s
  change (cubicCoordinateAlgebraEvaluation p hp (surfacePlaneJetCoordinates z v) hpJ s.1).fst =
    cubicCoordinateAlgebraEvaluation p hp z hpz s.1
  have h := congrArg TrivSqZeroExt.fst
    (surfacePlaneJet_projects_to_directionalJet z v (0 : Fin 2) q)
  simpa only [← hqs, cubicCoordinateAlgebraEvaluation_mk,
    TrivSqZeroExt.fst_map, homogeneousDirectionalJet_fst, MvPolynomial.aeval_def] using h

private theorem originalSurfaceJet_section_zero_iff001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) (z : Fin 4 → M) (hpz : p.eval₂ (algebraMap K M) z = 0)
    (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0)
    (hAnchor : surfacePlaneJetCoordinates z v j = 1)
    (s : cubicThroughCoordinateSections p hp n y hpy) :
    cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j s) = 0 ↔
      cubicThroughPointAuxiliaryEvaluation p hp n y hpy z hpz s = 0 ∧
      cubicThroughPointAuxiliaryTangentRestriction p hp n y hpy z v hpJ s = 0 := by
  rw [cubicNormalizedFullJetChartMap_section001]
  constructor
  · intro h
    constructor
    · have hf := congrArg TrivSqZeroExt.fst h
      rw [cubicGradeSurfaceJet_fst001 p hp n z hpz v hpJ s.1] at hf
      exact hf
    · exact congrArg TrivSqZeroExt.snd h
  · rintro ⟨hvalue, htangent⟩
    apply TrivSqZeroExt.ext
    · rw [cubicGradeSurfaceJet_fst001 p hp n z hpz v hpJ s.1]
      exact hvalue
    · exact htangent

/-- The literal native projective hyperplane contains the entire original
surface jet iff BOTH its ordinary value and its two tangent values vanish.
The actual Away map is constructed; no normalized-map comparison, tangent
noninclusion, reduced-support equality or regular curve is assumed. -/
theorem cubicThroughPointBasis_originalFullJet_nativeHyperplane_zero_iff001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) (z : Fin 4 → M) (hpz : p.eval₂ (algebraMap K M) z = 0)
    (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0)
    (hAnchor : surfacePlaneJetCoordinates z v j = 1)
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m)
    (ha : cubicThroughPointAuxiliaryEvaluation p hp n y hpy z hpz (b a) ≠ 0) :
    let I := equationIdeal p hp
    let R := ChartRing I j
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let x := fun i => e (b i)
    let gJ := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
    ∃ hUnit : IsUnit (gJ (x a)),
      let ell : Localization.Away (x a) →+* SurfacePlaneJet M :=
        IsLocalization.Away.lift (x a) hUnit
      ell.comp (algebraMap R (Localization.Away (x a))) = gJ ∧
      ∀ c : Fin m → K,
        ell (nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a
          (projectiveChartLinearForm a c)) = 0 ↔
          cubicThroughPointAuxiliaryEvaluation p hp n y hpy z hpz (∑ i, c i • b i) = 0 ∧
          cubicThroughPointAuxiliaryTangentRestriction p hp n y hpy z v hpJ (∑ i, c i • b i) = 0 := by
  classical
  let I := equationIdeal p hp
  let R := ChartRing I j
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let x := fun i => e (b i)
  let gJ := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  have hFst : (gJ (x a)).fst = cubicThroughPointAuxiliaryEvaluation p hp n y hpy z hpz (b a) := by
    rw [cubicNormalizedFullJetChartMap_section001]
    exact cubicGradeSurfaceJet_fst001 p hp n z hpz v hpJ (b a).1
  have hUnit : IsUnit (gJ (x a)) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    (isUnit_iff_ne_zero.mpr (by rw [hFst]; exact ha))
  refine ⟨hUnit, ?_⟩
  let ell : Localization.Away (x a) →+* SurfacePlaneJet M :=
    IsLocalization.Away.lift (x a) hUnit
  have hEll : ell.comp (algebraMap R (Localization.Away (x a))) = gJ :=
    IsLocalization.Away.lift_comp _ _
  refine ⟨hEll, ?_⟩
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
      (e (∑ i, c i • b i))) = gJ (e (∑ i, c i • b i)) :=
    RingHom.congr_fun hEll (e (∑ i, c i • b i))
  rw [hNumerator, hValue] at hKernel
  exact hKernel.trans
    (originalSurfaceJet_section_zero_iff001 p hp n y hpy j z hpz v hpJ hAnchor (∑ i, c i • b i))

end PfaffianDescent.Coray

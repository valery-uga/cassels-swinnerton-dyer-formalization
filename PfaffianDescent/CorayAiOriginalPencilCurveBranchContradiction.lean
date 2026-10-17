import PfaffianDescent.CorayAiNativePencilAttainedMemberPoint
import PfaffianDescent.CorayAiOriginalRatioBasisIntersectionAvoidance
import PfaffianDescent.CorayAiSameImageCurveBranchNativeCutContradiction

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Independence makes every actual pencil parameter a fresh section. -/
private theorem independentPencil_parameter_member_ne_zero001
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (s : Fin 2 → V) (hli : LinearIndependent K s) (t : K) :
    s 1 - t • s 0 ≠ 0 := by
  intro h
  have hValue : (1 : K) • s 1 = t • s 0 := by
    rw [one_smul]
    exact sub_eq_zero.mp h
  exact (by decide : (1 : Fin 2) ≠ 0)
    (hli.eq_of_smul_apply_eq_smul_apply 1 t 1 0 one_ne_zero hValue)

/-- Auxiliary ordinary value derives normalized value for the SAME
representative; this copy is a bounded independent caller cut. -/
private theorem pencilAuxiliarySection_native_value_zero001
    {K L M : Type u} [Field K] [Field L] [Algebra K L] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (gA : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (hpz : p.eval₂ (algebraMap K M)
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
    (v : cubicThroughCoordinateSections p hp n y hpy)
    (hAux : cubicThroughPointAuxiliaryEvaluation p hp n y hpy
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) hpz v = 0) :
    gA (cubicThroughPointChartEvaluation p hp n y hpy j v) = 0 := by
  obtain ⟨q, hq, _, hClass⟩ :=
    (cubicThroughCoordinateSections_mem_iff p hp n y hpy v.1).mp v.2
  have hOrdinary : q.eval₂ (algebraMap K M)
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0 := by
    change cubicCoordinateAlgebraEvaluation p hp
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) hpz v.1.1 = 0 at hAux
    rw [← hClass] at hAux
    exact hAux
  rw [← cubicThroughPointSection_polynomial_normalized_eq_chartEvaluation001
    p hp n y hpy j v q hq hClass, MvPolynomial.hom_eval₂, hBase]
  exact hOrdinary

/-- A nonzero actual module element has nonzero coefficients in every full
basis. The entire representation argument is checked before specializing to
original cubic sections. -/
private theorem basis_member_coefficients_sum_and_ne_zero001
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    {m : ℕ} (b : Module.Basis (Fin m) K V) (v : V) (hv : v ≠ 0) :
    (∑ i, (b.repr v i) • b i) = v ∧ (fun i => b.repr v i) ≠ 0 := by
  refine ⟨b.sum_repr v, ?_⟩
  intro h
  have hRepr : b.repr v = 0 := by
    ext i
    exact congrFun h i
  apply hv
  exact b.repr.injective (hRepr.trans (map_zero b.repr).symm)

/-- Specialize pencil independence to the original section module in a
bounded declaration without the auxiliary field, projective image or pullback
context. The actual caller receives the original member itself. -/
private theorem originalSectionIndependentPencil_parameter_member_ne_zero001
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (s : Fin 2 → cubicThroughCoordinateSections p hp n y hpy)
    (hli : LinearIndependent K s) (t : K) :
    s 1 - t • s 0 ≠ 0 := by
  intro h
  have hValue : (1 : K) • s 1 = t • s 0 := by
    rw [one_smul]
    exact sub_eq_zero.mp h
  exact (by decide : (1 : Fin 2) ≠ 0)
    (hli.eq_of_smul_apply_eq_smul_apply 1 t 1 0 one_ne_zero hValue)

/-- Ordinary linear-map evaluation of an independent-pencil member,
checked without the original graded-chart module-conversion frame. -/
private theorem linearPencil_evaluation_sub_smul001
    {K V A : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup A] [Module K A]
    (e : V →ₗ[K] A) (s : Fin 2 → V) (t : K) :
    e (s 1 - t • s 0) = e (s 1) - t • e (s 0) := by
  rw [e.map_sub, e.map_smul]

/-- Exact native hyperplane membership is specialized only after its
numerator membership is known; the whole four-part dictionary stays outside
the original cubic caller's conversion context. -/
private theorem nativeHyperplane_mem_of_numerator_mem001
    {K R : Type u} [CommRing K] [CommRing R] {σ : Type} [Fintype σ]
    (f : K →+* R) (x : σ → R) (a : σ) (c : σ → K)
    (z : Spec (.of (Localization.Away (x a))))
    (h : algebraMap R (Localization.Away (x a)) (∑ i, f (c i) * x i) ∈ z.asIdeal) :
    nativeLocalizedProjectiveChartMap f x a (projectiveChartLinearForm a c) ∈ z.asIdeal := by
  exact ((nativeLocalizedProjectiveChartMap_hyperplane_pullback001 f x a).2.2.2
    c z.asIdeal).mpr h

/-- Transport an exact numerator equality before specializing native
hyperplane membership to the original chart. The equality rewrite is checked
with abstract R, outside the original quotient/basis conversion frame. -/
private theorem nativeHyperplane_mem_of_section_numerator001
    {K R : Type u} [CommRing K] [CommRing R] {σ : Type} [Fintype σ]
    (f : K →+* R) (x : σ → R) (a : σ) (c : σ → K)
    (z : Spec (.of (Localization.Away (x a)))) (r : R)
    (hNum : (∑ i, f (c i) * x i) = r)
    (hMem : algebraMap R (Localization.Away (x a)) r ∈ z.asIdeal) :
    nativeLocalizedProjectiveChartMap f x a (projectiveChartLinearForm a c) ∈ z.asIdeal := by
  apply nativeHyperplane_mem_of_numerator_mem001 f x a c z
  rw [hNum]
  exact hMem

/-- Distinct projected images are transported only by literal projection
identities. This generic function argument avoids rewriting inside the actual
original cubic and scheme-pullback conversion context. -/
private theorem functionImages_distinct_of_projection_equalities001
    {X Y Z : Type u} (f : Y → Z) (π : X → Y)
    (x₀ x₁ : X) (y₀ y₁ : Y)
    (h₀ : π x₀ = y₀) (h₁ : π x₁ = y₁) (hNe : f y₁ ≠ f y₀) :
    f (π x₀) ≠ f (π x₁) := by
  rw [h₀, h₁]
  exact hNe.symm

/-- The two literal native hyperplane pullback points and their distinct
images are constructed together in an abstract ring frame. Both exact first
projections are retained; the original caller need not reconvert them. -/
private theorem nativeHyperplanePullback_exists_two_distinctProjectedImages001
    {K R : Type u} [CommRing K] [CommRing R] {σ : Type} [Fintype σ]
    (f : K →+* R) (x : σ → R) (a : σ) (c : σ → K)
    (z₀ z₁ : Spec (.of (Localization.Away (x a))))
    (h₀ : nativeLocalizedProjectiveChartMap f x a (projectiveChartLinearForm a c) ∈ z₀.asIdeal)
    (h₁ : nativeLocalizedProjectiveChartMap f x a (projectiveChartLinearForm a c) ∈ z₁.asIdeal)
    (hNe : nativeLocalizedProjectiveChartPoint f x a z₀ ≠
      nativeLocalizedProjectiveChartPoint f x a z₁) :
    let A := ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K)) a
    let H := Ideal.span ({projectiveChartLinearForm a c} : Set A)
    let v := Spec.map (CommRingCat.ofHom (nativeLocalizedProjectiveChartMap f x a))
    let h := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))
    let Phi := nativeLocalizedProjectiveChartPoint f x a
    ∃ w₀ w₁ : (pullback v h : Scheme),
      pullback.fst v h w₀ = z₀ ∧ pullback.fst v h w₁ = z₁ ∧
      Phi (pullback.fst v h w₀) ≠ Phi (pullback.fst v h w₁) := by
  intro A H v h Phi
  let π : (pullback v h : Scheme) ⟶ Spec (.of (Localization.Away (x a))) := pullback.fst v h
  obtain ⟨w₀, hw₀⟩ : ∃ w : (pullback v h : Scheme), π w = z₀ :=
    nativeLocalizedProjectiveHyperplanePullback_exists_point_above001 f x a c z₀ h₀
  obtain ⟨w₁, hw₁⟩ : ∃ w : (pullback v h : Scheme), π w = z₁ :=
    nativeLocalizedProjectiveHyperplanePullback_exists_point_above001 f x a c z₁ h₁
  refine ⟨w₀, w₁, hw₀, hw₁, ?_⟩
  exact functionImages_distinct_of_projection_equalities001
    (fun z => Phi z) (fun w => π w) w₀ w₁ z₀ z₁ hw₀ hw₁ hNe.symm

/-- Transport the SAME representative class to ordinary polynomial
value in a thin original-section frame. The quotient evaluation identity is
applied explicitly, before returning to the image/pullback context. -/
private theorem originalSection_polynomial_value_zero_of_class001
    {K L M : Type u} [Field K] [Field L] [Algebra K L] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (x : Fin 4 → M) (hpx : p.eval₂ (algebraMap K M) x = 0)
    (v : cubicThroughCoordinateSections p hp n y hpy)
    (q : MvPolynomial (Fin 4) K)
    (hClass : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = v.1.1)
    (hValue : cubicThroughPointAuxiliaryEvaluation p hp n y hpy x hpx v = 0) :
    q.eval₂ (algebraMap K M) x = 0 := by
  calc
    _ = cubicCoordinateAlgebraEvaluation p hp x hpx
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal q) :=
      (cubicCoordinateAlgebraEvaluation_mk p hp x hpx q).symm
    _ = cubicCoordinateAlgebraEvaluation p hp x hpx v.1.1 :=
      congrArg (cubicCoordinateAlgebraEvaluation p hp x hpx) hClass
    _ = 0 := hValue

/-- In the honest image-CURVE branch, the actual original independent
P/A pencil internally attains an original-K parameter away from the ENTIRE
original auxiliary image. Both points are lifted into the literal native
hyperplane pullback. The SAME full original member is then nonintegral.
The image dimension hypothesis is explicit; no surface-dimension claim is
inferred from nondegeneracy or one transcendental ratio. -/
theorem originalIndependentPencil_curveBranch_exists_nonintegralWholeMember001
    {K L M : Type u} [Field K] [Infinite K] [Field L] [Algebra K L]
    [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (s : Fin 2 → cubicThroughCoordinateSections p hp n y hpy)
    (hli : LinearIndependent K s)
    (gA : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : gA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (hpz : p.eval₂ (algebraMap K M)
      (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0)
    (hAux : ∀ i, cubicThroughPointAuxiliaryEvaluation p hp n y hpy
      (fun k => gA (chartCoordinate (equationIdeal p hp) j k)) hpz (s i) = 0)
    (a : Fin m)
    (ha : gA (cubicThroughPointChartEvaluation p hp n y hpy j (b a)) ≠ 0)
    (hDim : ∀ z : cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a,
      Ring.DimensionLEOne
        ((cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a).presheaf.stalk z)) :
    ∃ (t : K) (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
      q.eval₂ (algebraMap K L) y = 0 ∧
      q.eval₂ (algebraMap K M)
        (fun i => gA (chartCoordinate (equationIdeal p hp) j i)) = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = (s 1 - t • s 0).1.1 ∧
      ¬ IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) := by
  classical
  let I := equationIdeal p hp
  let R := ChartRing I j
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let x := fun i => e (b i)
  let x₀ := e (s 0)
  let B := Localization.Away x₀
  let C := Localization.Away (algebraMap R B (x a))
  let k := nativePencilBasisIntersectionToRatio001 x₀ (x a)
  let gamma := nativePencilBasisIntersectionToBasis001 x₀ (x a)
  let f₀ := nativeLocalizedPencilAffineLineMap001 (chartBaseMap I j) x₀ (e (s 1))
  let beta := nativePencilBasisIntersectionBasisHom001 x₀ (x a)
  let ell : Localization.Away (x a) →+* M :=
    IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr ha)
  let zA := Spec.map (CommRingCat.ofHom ell) (IsLocalRing.closedPoint M)
  let Phi := nativeLocalizedProjectiveChartPoint (chartBaseMap I j) x a
  obtain ⟨_hIC, _hOI, hD, hFT, hQC, _hOver, _hSquare, _hRange, hAvoid⟩ :=
    originalIndependentPencil_fixedBasisIntersection_avoids_auxiliaryImage001
      p hp hp0 n y hpy j b s hli gA hBase hpz hAux a ha
  letI : IsDominant (k ≫ f₀) := hD
  letI : LocallyOfFiniteType (k ≫ f₀) := hFT
  letI : QuasiCompact (k ≫ f₀) := hQC
  obtain ⟨t, z, hMemberPrime, _hAttained⟩ :=
    nativeLocalizedPencilAffineLine_exists_attained_memberPrime001
      (chartBaseMap I j) x₀ (e (s 1)) k
  let v : cubicThroughCoordinateSections p hp n y hpy := s 1 - t • s 0
  let c : Fin m → K := fun i => b.repr v i
  have hFresh : v ≠ 0 :=
    originalSectionIndependentPencil_parameter_member_ne_zero001 p hp n y hpy s hli t
  have hBasis := basis_member_coefficients_sum_and_ne_zero001 b v hFresh
  have hSum : (∑ i, c i • b i) = v := hBasis.1
  have hc : c ≠ 0 := hBasis.2
  have hEv : e v = e (s 1) - chartBaseMap I j t * x₀ := by
    calc
      e v = e (s 1) - t • e (s 0) := linearPencil_evaluation_sub_smul001 e s t
      _ = e (s 1) - chartBaseMap I j t * x₀ := by
        rw [gradedChartNative_smul_eq_baseMap_mul (grading I)]
        rfl
  have hNumerator : (∑ i, chartBaseMap I j (c i) * x i) = e v := by
    calc
      _ = e (∑ i, c i • b i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        exact (gradedChartNative_smul_eq_baseMap_mul (grading I) (c i) (e (b i))).symm
      _ = _ := congrArg e hSum
  have hAuxV : cubicThroughPointAuxiliaryEvaluation p hp n y hpy
      (fun i => gA (chartCoordinate I j i)) hpz v = 0 := by
    have h := linearPencil_evaluation_sub_smul001
      (cubicThroughPointAuxiliaryEvaluation p hp n y hpy
        (fun i => gA (chartCoordinate I j i)) hpz) s t
    exact h.trans (by rw [hAux 1, hAux 0, smul_zero, sub_self])
  have hNativeA : gA (e v) = 0 :=
    pencilAuxiliarySection_native_value_zero001 p hp n y hpy j gA hBase hpz v hAuxV
  let theta := nativeLocalizedProjectiveChartMap (chartBaseMap I j) x a
  have hThetaA : theta (projectiveChartLinearForm a c) ∈ zA.asIdeal := by
    change ell (theta (projectiveChartLinearForm a c)) ∈ (IsLocalRing.closedPoint M).asIdeal
    simp only [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
    rw [(nativeLocalizedProjectiveChartMap_hyperplane_pullback001
      (chartBaseMap I j) x a).2.2.1 c, hNumerator, map_mul,
      IsLocalization.Away.lift_eq, hNativeA, zero_mul]
  have hGammaNumerator : algebraMap R (Localization.Away (x a)) (e v) ∈
      (gamma z).asIdeal := by
    change beta (algebraMap R (Localization.Away (x a)) (e v)) ∈ z.asIdeal
    dsimp only [beta, nativePencilBasisIntersectionBasisHom001]
    rw [IsLocalization.Away.lift_eq]
    change algebraMap R B (e v) ∈ (k z).asIdeal
    rw [hEv]
    exact hMemberPrime
  have hThetaZ : theta (projectiveChartLinearForm a c) ∈ (gamma z).asIdeal :=
    nativeHyperplane_mem_of_section_numerator001 (chartBaseMap I j) x a c (gamma z)
      (e v) hNumerator hGammaNumerator
  have hAvoidHere : Phi (gamma z) ≠ Phi zA := hAvoid z
  obtain ⟨wZ, wA, _hZproj, _hAproj, hDistinct⟩ :=
    nativeHyperplanePullback_exists_two_distinctProjectedImages001
      (chartBaseMap I j) x a c (gamma z) zA hThetaZ hThetaA hAvoidHere
  obtain ⟨q, hq, hP, hnot, hClass, hWhole⟩ :=
    cubicThroughPointBasis_curveBranch_twoNativeCutImages_exists_nonintegralWholeMember001
      p hp hp0 n y hpy j b a c hc hDim wZ wA hDistinct
  have hClassV : Ideal.Quotient.mk I.toIdeal q = v.1.1 :=
    hClass.trans (congrArg (fun w : cubicThroughCoordinateSections p hp n y hpy => w.1.1) hSum)
  have hQA : q.eval₂ (algebraMap K M) (fun i => gA (chartCoordinate I j i)) = 0 :=
    originalSection_polynomial_value_zero_of_class001 p hp n y hpy
      (fun i => gA (chartCoordinate I j i)) hpz v q hClassV hAuxV
  exact ⟨t, q, hq, hP, hQA, hnot, hClassV, hWhole⟩

end PfaffianDescent.Coray

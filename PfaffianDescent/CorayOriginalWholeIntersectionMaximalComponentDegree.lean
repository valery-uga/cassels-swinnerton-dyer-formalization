import PfaffianDescent.VoisinRegularLocalDepth
import PfaffianDescent.VoisinRegularSequenceCriteria
import PfaffianDescent.CorayHomogeneousProjectiveComponentBijection
import PfaffianDescent.CorayWholeSurfaceIdealGradeHilbertRank
import PfaffianDescent.CorayOwnMinimalComponentDegreePositiveAnyField
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-! Whole original complete-intersection degree equality, without radical replacement.
A nonzero element of the component kernel supplies a second positive Hilbert
contribution via an actual associated minimal prime. This also detects a
single minimal component with nonreduced multiplicity. Source only. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Compare two actual image ranks using inclusion of their kernels. -/
private theorem componentKernel_image_rank_lower
    {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module K M] [Module K N] [Module K P] [Module.Finite K M] [Module.Finite K N]
    (f : M →ₗ[K] N) (g : M →ₗ[K] P)
    (hker : f.ker ≤ g.ker) (hg : Function.Surjective g) :
    finrank K P ≤ finrank K N := by
  letI : Module.Finite K P := Module.Finite.of_surjective g hg
  have hf := f.finrank_range_add_finrank_ker
  have hgs := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hg, finrank_top] at hgs
  have hk := Submodule.finrank_mono hker
  have hr := Submodule.finrank_le (LinearMap.range f)
  omega

/-- Original smooth cubic and arbitrary positive-degree second equation
produce unmixedness of the WHOLE quotient, including nilpotents. -/
theorem originalWholeIntersection_associatedPrime_minimal001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (Q : Ideal (MvPolynomial (Fin 4) K))
    (hQ : Q ∈ associatedPrimes (MvPolynomial (Fin 4) K)
      (CoordinateRing (projectiveIntersectionIdeal p q hp hq))) :
    Q ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes := by
  have hpPrime : Prime p := (Ideal.span_singleton_prime hp0).mp
    (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  have hrel := isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot
  have hreg := PfaffianDescent.homogeneous_pair_isRegular_of_prime_of_isRelPrime
    hp hq (by decide : 0 < 3) (by omega : 0 < n) hpPrime hrel
  have hPair : Ideal.ofList [p, q] =
      (projectiveIntersectionIdeal p q hp hq).toIdeal := by
    rw [projectiveIntersectionIdeal_toIdeal]
    simp only [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq, Ideal.span_insert]
  have hAssoc : Q ∈ associatedPrimes (MvPolynomial (Fin 4) K)
      (MvPolynomial (Fin 4) K ⧸ Ideal.ofList [p, q]) := by
    change Q ∈ associatedPrimes (MvPolynomial (Fin 4) K)
      (MvPolynomial (Fin 4) K ⧸ (projectiveIntersectionIdeal p q hp hq).toIdeal) at hQ
    rw [hPair]
    exact hQ
  have hMin := PfaffianDescent.regularRing_associatedPrime_quotient_ofList_mem_minimalPrimes
    (MvPolynomial (Fin 4) K) [p, q] hreg.toIsWeaklyRegular Q hAssoc
  simpa only [hPair] using hMin

/-- A nonzero class in the actual WHOLE quotient supplies a genuine
homogeneous minimal component containing its annihilator. No reduction. -/
theorem originalWholeIntersection_nonzeroClass_exists_minimalAnnihilatorComponent001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (F : MvPolynomial (Fin 4) K)
    (hF : F ∉ (projectiveIntersectionIdeal p q hp hq).toIdeal) :
    ∃ Q : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      Q.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes ∧
      ∀ a : MvPolynomial (Fin 4) K,
        F * a ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal → a ∈ Q.toIdeal := by
  let J := projectiveIntersectionIdeal p q hp hq
  have hF0 : Ideal.Quotient.mk J.toIdeal F ≠ 0 := by
    intro hz
    exact hF (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  obtain ⟨P, hAssoc, hAnn⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing
    (MvPolynomial (Fin 4) K) (Ideal.Quotient.mk J.toIdeal F) hF0
  have hMin := originalWholeIntersection_associatedPrime_minimal001
    p q hp hp0 n hn hq hnot P hAssoc
  let Q := P.homogeneousCore (homogeneousSubmodule (Fin 4) K)
  have hQP : Q.toIdeal = P := homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal J P hMin
  refine ⟨Q, hQP.symm ▸ hMin, ?_⟩
  intro a ha
  rw [hQP]
  apply hAnn
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change Ideal.Quotient.mk J.toIdeal a * Ideal.Quotient.mk J.toIdeal F = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  simpa only [mul_comm] using ha

/-- Multiplication by the SAME homogeneous kernel element, landing in
the ACTUAL quotient-grade kernel. -/
private def componentKernelHomogeneousMultiplication
    (J I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hJI : J.toIdeal ≤ I.toIdeal) (F : MvPolynomial (Fin 4) K) (e : ℕ)
    (hFe : F.IsHomogeneous e) (hFI : F ∈ I.toIdeal) (m : ℕ) :
    grading J m →ₗ[K] (homogeneousCoordinateQuotientGradeMap J I hJI (e + m)).ker where
  toFun x := ⟨⟨Ideal.Quotient.mk J.toIdeal F * x.val,
    SetLike.mul_mem_graded (show Ideal.Quotient.mk J.toIdeal F ∈ grading J e from
      ⟨F, hFe, rfl⟩) x.property⟩, by
      apply Subtype.ext
      change (Ideal.Quotient.factor hJI) (Ideal.Quotient.mk J.toIdeal F * x.val) = 0
      rw [map_mul, Ideal.Quotient.factor_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr hFI, zero_mul]⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_smul_comm _ _ _

/-- Finite actual homogeneous quotient grade, isolated from kernel maps. -/
private theorem componentKernel_grade_finite004
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (m : ℕ) :
    Module.Finite K (grading J m) := by
  change Module.Finite K ((homogeneousSubmodule (Fin 4) K m).map
    (Ideal.Quotient.mkₐ K J.toIdeal).toLinearMap)
  infer_instance

/-- The actual multiplication kernel annihilates the SAME quotient class. -/
private theorem componentKernelHomogeneousMultiplication_zero_of_mem_ker004
    (J I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hJI : J.toIdeal ≤ I.toIdeal) (F : MvPolynomial (Fin 4) K) (e : ℕ)
    (hFe : F.IsHomogeneous e) (hFI : F ∈ I.toIdeal) (m : ℕ)
    (x : grading J m)
    (hx : x ∈ (componentKernelHomogeneousMultiplication J I hJI F e hFe hFI m).ker) :
    Ideal.Quotient.mk J.toIdeal F * x.val = 0 := by
  exact congrArg (fun y => y.val.val) hx

/-- The literal annihilator inclusion gives the actual map-kernel inclusion. -/
private theorem componentKernelHomogeneousMultiplication_kernel_le004
    (J I Q : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hJI : J.toIdeal ≤ I.toIdeal) (hJQ : J.toIdeal ≤ Q.toIdeal)
    (F : MvPolynomial (Fin 4) K) (e : ℕ) (hFe : F.IsHomogeneous e)
    (hFI : F ∈ I.toIdeal)
    (hAnn : ∀ a : MvPolynomial (Fin 4) K, F * a ∈ J.toIdeal → a ∈ Q.toIdeal)
    (m : ℕ) :
    (componentKernelHomogeneousMultiplication J I hJI F e hFe hFI m).ker ≤
      (homogeneousCoordinateQuotientGradeMap J Q hJQ m).ker := by
  intro x hx
  have hZero := componentKernelHomogeneousMultiplication_zero_of_mem_ker004
    J I hJI F e hFe hFI m x hx
  obtain ⟨a, _ha, hax⟩ := x.property
  change Ideal.Quotient.mk J.toIdeal a = x.val at hax
  have hFa : F * a ∈ J.toIdeal := by
    rw [← hax, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hZero
    exact hZero
  have haQ := hAnn a hFa
  apply Subtype.ext
  change (Ideal.Quotient.factor hJQ) x.val = 0
  rw [← hax, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr haQ]

/-- Fix the actual source/target module types BEFORE any multiplication
map is supplied. Finite-grade assumptions are ordinary dictionaries. -/
private theorem componentKernel_quotientRank_lower006
    (J I Q : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hJI : J.toIdeal ≤ I.toIdeal) (hJQ : J.toIdeal ≤ Q.toIdeal) (e m : ℕ)
    [Module.Finite K (grading J m)] [Module.Finite K (grading J (e + m))]
    (f : grading J m →ₗ[K] (homogeneousCoordinateQuotientGradeMap J I hJI (e + m)).ker)
    (hKer : f.ker ≤ (homogeneousCoordinateQuotientGradeMap J Q hJQ m).ker) :
    finrank K (grading Q m) ≤
      finrank K (homogeneousCoordinateQuotientGradeMap J I hJI (e + m)).ker := by
  let g := homogeneousCoordinateQuotientGradeMap J Q hJQ m
  have hSurj := homogeneousCoordinateQuotientGradeMap_surjective J Q hJQ m
  have hRank := componentKernel_image_rank_lower
    (M := grading J m)
    (N := (homogeneousCoordinateQuotientGradeMap J I hJI (e + m)).ker)
    (P := grading Q m) f g hKer hSurj
  exact hRank

/-- Rank comparison uses only the two actual maps and their checked kernels. -/
private theorem componentKernelHomogeneousMultiplication_finrank_lower004
    (J I Q : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hJI : J.toIdeal ≤ I.toIdeal) (hJQ : J.toIdeal ≤ Q.toIdeal)
    (F : MvPolynomial (Fin 4) K) (e : ℕ) (hFe : F.IsHomogeneous e)
    (hFI : F ∈ I.toIdeal)
    (hAnn : ∀ a : MvPolynomial (Fin 4) K, F * a ∈ J.toIdeal → a ∈ Q.toIdeal)
    (m : ℕ) :
    finrank K (grading Q m) ≤
      finrank K (homogeneousCoordinateQuotientGradeMap J I hJI (e + m)).ker := by
  letI : Module.Finite K (grading J m) := componentKernel_grade_finite004 J m
  letI : Module.Finite K (grading J (e + m)) := componentKernel_grade_finite004 J (e + m)
  let f := componentKernelHomogeneousMultiplication J I hJI F e hFe hFI m
  have hKer := componentKernelHomogeneousMultiplication_kernel_le004
    J I Q hJI hJQ F e hFe hFI hAnn m
  have hRank := componentKernel_quotientRank_lower006 J I Q hJI hJQ e m f hKer
  exact hRank

/-- Combine the checked lower rank with the SAME literal whole-ideal balance. -/
private theorem componentKernelHomogeneousMultiplication_grade_balance004
    (J I Q : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hJI : J.toIdeal ≤ I.toIdeal) (hJQ : J.toIdeal ≤ Q.toIdeal)
    (F : MvPolynomial (Fin 4) K) (e : ℕ) (hFe : F.IsHomogeneous e)
    (hFI : F ∈ I.toIdeal)
    (hAnn : ∀ a : MvPolynomial (Fin 4) K, F * a ∈ J.toIdeal → a ∈ Q.toIdeal)
    (m : ℕ) :
    finrank K (grading I (e + m)) + finrank K (grading Q m) ≤
      finrank K (grading J (e + m)) := by
  have hRank := componentKernelHomogeneousMultiplication_finrank_lower004
    J I Q hJI hJQ F e hFe hFI hAnn m
  have hBalance := homogeneousQuotientGrade_finrank_add_wholeIdealGrade J I hJI (e + m)
  have hKernelEq := (homogeneousQuotientGradeKernelWholeIdealEquiv J I hJI (e + m)).finrank_eq
  omega

/-- A nonzero homogeneous component-kernel element forces a second
positive-grade contribution, even if Q is the SAME component as I. -/
theorem originalWholeIntersection_nonzeroComponentKernel_gradeLowerBound001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (F : MvPolynomial (Fin 4) K) (e : ℕ) (hFe : F.IsHomogeneous e)
    (hFI : F ∈ I.toIdeal) (hFJ : F ∉ (projectiveIntersectionIdeal p q hp hq).toIdeal) :
    ∃ Q : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      Q.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes ∧
      ∀ m : ℕ, finrank K (grading I (e + m)) + finrank K (grading Q m) ≤
        finrank K (grading (projectiveIntersectionIdeal p q hp hq) (e + m)) := by
  obtain ⟨Q, hQ, hAnn⟩ := originalWholeIntersection_nonzeroClass_exists_minimalAnnihilatorComponent001
    p q hp hp0 n hn hq hnot F hFJ
  refine ⟨Q, hQ, ?_⟩
  intro m
  exact componentKernelHomogeneousMultiplication_grade_balance004
    (projectiveIntersectionIdeal p q hp hq) I Q hI.le hQ.le F e hFe hFI hAnn m

/-- Eventual increments give the actual affine values above any common base. -/
private theorem componentKernel_eventualIncrement_affine
    (a : ℕ → ℕ) (mu N : ℕ)
    (h : ∀ m : ℕ, N ≤ m → a (m + 1) = a m + mu)
    (B : ℕ) (hB : N ≤ B) (t : ℕ) : a (B + t) = a B + t * mu := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hs := h (B + t) (by omega)
    rw [ih] at hs
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_mul, one_mul] using hs

/-- Equality with the WHOLE complete-intersection degree forces literal
ideal equality, not only radical equality. Single-component nilpotents are
excluded by the second positive kernel contribution. -/
theorem selectedOriginalWholeIntersection_maximalComponentDegree_ideal_eq001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hDegree : actualCurveCoordinateHilbertDegree I = 3 * n) :
    projectiveIntersectionIdeal p q hp hq = I := by
  classical
  let J := projectiveIntersectionIdeal p q hp hq
  by_contra hEq
  have hex : ∃ F : MvPolynomial (Fin 4) K, F ∈ I.toIdeal ∧ F ∉ J.toIdeal := by
    by_contra h
    apply hEq
    apply HomogeneousIdeal.ext
    apply le_antisymm hI.le
    intro F hFI
    by_contra hFJ
    exact h ⟨F, hFI, hFJ⟩
  obtain ⟨F, hFI, hFJ⟩ := hex
  have hComponents : ¬ ∀ e : ℕ, homogeneousComponent e F ∈ J.toIdeal := by
    intro hAll
    exact hFJ ((mem_iff_homogeneousComponent_mem J.isHomogeneous F).mpr hAll)
  push_neg at hComponents
  obtain ⟨e, hFeJ⟩ := hComponents
  let f := homogeneousComponent e F
  have hfe : f.IsHomogeneous e := homogeneousComponent_mem e F
  have hfI : f ∈ I.toIdeal := homogeneousComponent_mem_of_mem I.isHomogeneous hFI e
  obtain ⟨Q, hQ, hLower⟩ := originalWholeIntersection_nonzeroComponentKernel_gradeLowerBound001
    p q hp hp0 n hn hq hnot I hI f e hfe hfI hFeJ
  obtain ⟨_hPosI, _hBoundI, NI, hIncI⟩ :=
    selectedProjectiveMinimalComponent_hilbertDegree_pos_bound_and_eventualIncrement_anyField
      p q hp hp0 n hq hnot I hI
  obtain ⟨hPosQ, _hBoundQ, NQ, hIncQ⟩ :=
    selectedProjectiveMinimalComponent_hilbertDegree_pos_bound_and_eventualIncrement_anyField
      p q hp hp0 n hq hnot Q hQ
  let N := max NI (max NQ (n + 3))
  let t := 3 * n * (e + N) + 1
  have hNI : NI ≤ e + N := by
    have h := Nat.le_max_left NI (max NQ (n + 3))
    omega
  have hNQ : NQ ≤ N := (Nat.le_max_left NQ (n + 3)).trans (Nat.le_max_right NI _)
  have hBase : n + 3 ≤ N := (Nat.le_max_right NQ (n + 3)).trans (Nat.le_max_right NI _)
  have hGrowI := componentKernel_eventualIncrement_affine
    (fun d => finrank K (grading I d)) (actualCurveCoordinateHilbertDegree I)
    NI hIncI (e + N) hNI t
  have hGrowQ := componentKernel_eventualIncrement_affine
    (fun d => finrank K (grading Q d)) (actualCurveCoordinateHilbertDegree Q)
    NQ hIncQ N hNQ t
  have hLowerAt := hLower (N + t)
  have hGrowI' : finrank K (grading I (e + (N + t))) =
      finrank K (grading I (e + N)) + t * (3 * n) := by
    change finrank K (grading I (e + N + t)) =
      finrank K (grading I (e + N)) + t * actualCurveCoordinateHilbertDegree I at hGrowI
    rw [hDegree] at hGrowI
    have hIndexRank := congrArg (fun d : ℕ => finrank K (grading I d))
      (Nat.add_assoc e N t)
    exact hIndexRank.symm.trans hGrowI
  rw [hGrowI', hGrowQ] at hLowerAt
  have hIndex : e + (N + t) - (n + 3) + n + 3 = e + (N + t) := by omega
  have hUpper := selectedProjectiveComponent_hilbertFunction_linearBound
    p q hp hp0 n hn hq hnot J le_rfl (e + (N + t) - (n + 3))
  rw [hIndex] at hUpper
  have hQMul : t ≤ t * actualCurveCoordinateHilbertDegree Q := by
    simpa only [mul_one] using Nat.mul_le_mul_left t (show 1 ≤ actualCurveCoordinateHilbertDegree Q by omega)
  have hSlope : 2 * t ≤ 6 * n * (e + N) := by
    nlinarith only [hLowerAt, hUpper, hQMul,
      Nat.zero_le (finrank K (grading I (e + N))),
      Nat.zero_le (finrank K (grading Q N)), Nat.zero_le (3 * n * (n - 1))]
  have hSix : 6 * n * (e + N) = 2 * (3 * n * (e + N)) := by ring
  rw [hSix] at hSlope
  dsimp only [t] at hSlope
  omega

/-- The equality-degree branch gives integrality of the literal WHOLE
scheme. No reducedness, radicality, saturation or integrality premise. -/
theorem selectedOriginalWholeIntersection_maximalComponentDegree_isIntegral001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hDegree : actualCurveCoordinateHilbertDegree I = 3 * n) :
    IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) := by
  have hEq := selectedOriginalWholeIntersection_maximalComponentDegree_ideal_eq001
    p q hp hp0 n hn hq hnot I hI hDegree
  have hRel := selectedProjectiveMinimalComponent_homogeneous_relevant
    p q hp hp0 n hq hnot I hI
  have hInt : IsIntegral (scheme I) :=
    (homogeneousMinimalPrime_projective_reducedComponent
      (projectiveIntersectionIdeal p q hp hq) I hI hRel).2.1
  simpa only [hEq] using hInt

/-- Genuine nonintegral whole intersections have strict own degree on
EVERY selected minimal component, including a nonreduced single component. -/
theorem selectedOriginalWholeIntersection_nonintegral_minimalComponent_degree_lt001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (hNonIntegral : ¬ IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    actualCurveCoordinateHilbertDegree I < 3 * n := by
  have hBound := (selectedProjectiveMinimalComponent_hilbertDegree_pos_bound_and_eventualIncrement_anyField
    p q hp hp0 n hq hnot I hI).2.1
  have hNe : actualCurveCoordinateHilbertDegree I ≠ 3 * n := by
    intro hEq
    exact hNonIntegral (selectedOriginalWholeIntersection_maximalComponentDegree_isIntegral001
      p q hp hp0 n hn hq hnot I hI hEq)
  omega

end PfaffianDescent.Coray

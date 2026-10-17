import PfaffianDescent.CorayComponentAiiRegularity
import PfaffianDescent.CorayOwnComponentWordSection
import PfaffianDescent.CorayOwnComponentWordCycle
import PfaffianDescent.CorayComponentOwnNormalizationCycle
import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint
import PfaffianDescent.CoraySelectedCurveOriginalPointIncidenceLift
import PfaffianDescent.CoraySignedCycleWordDegreeSelection

/-! Source-only: literal OWN component words and original-point A(ii)
closure, without any integral/GI/reducedness assumption on the whole curve. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal SAME-normalization cycles of degrees d and OWN mu suffice in
A(ii)'s coarse G_n window when mu is a positive multiple3 bounded by3n.
There is no false mu|3n hypothesis and no canonical-divisor input. -/
theorem coray_case_Aii_ownDegreeCycles_choose_word
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (n d mu : ℕ)
    (hn : 3 ≤ n) (hd : 0 < d) (hprime : ¬ 3 ∣ d)
    (hmu : 0 < mu) (hmuThree : 3 ∣ mu) (hmuBound : mu ≤ 3 * n)
    (hdegree : d ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 - d < 3)
    (zD zH : ZeroCycle X) (hD : ZeroCycle.degree pi zD = (d : ℤ))
    (hH : ZeroCycle.degree pi zH = (mu : ℤ)) :
    ∃ (theta : ℕ) (ops : List (closedPoints X × Bool)),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = (theta : ℤ) ∧
        0 < theta ∧ ¬ 3 ∣ theta ∧ 3 * n.choose 2 + 1 ≤ theta ∧ theta < d := by
  let delta := Nat.gcd d mu
  have hdelta : 0 < delta := Nat.gcd_pos_of_pos_left _ hd
  have hdeltaD : delta ∣ d := Nat.gcd_dvd_left _ _
  have hdeltaH : delta ∣ mu := Nat.gcd_dvd_right _ _
  have hdeltaPrime : ¬ 3 ∣ delta := fun h => hprime (dvd_trans h hdeltaD)
  obtain ⟨lambda, hlambda⟩ := hmuThree
  have hlambdaPos : 0 < lambda := by rw [hlambda] at hmu; omega
  have hlambdaBound : lambda ≤ n := by rw [hlambda] at hmuBound; omega
  have hdeltaLambda : delta ∣ lambda :=
    degree_delta_dvd_l_of_dvd_three_l delta lambda hdeltaPrime (hlambda ▸ hdeltaH)
  have hdeltaBound : delta ≤ n := (Nat.le_of_dvd hlambdaPos hdeltaLambda).trans hlambdaBound
  obtain ⟨theta, hpos, hmultiple, hprimeTheta, hlow, hhigh⟩ :=
    exists_positive_multiple_prime_to_three_in_genus_window delta (3 * n.choose 2 + 1)
      hdelta hdeltaPrime
  have hstep : 3 * (n + 1).choose 2 = 3 * n.choose 2 + 3 * n := by
    simpa only [Nat.reduceAdd, Nat.choose_one_right, Nat.mul_add, Nat.add_comm] using
      congrArg (fun t : ℕ => 3 * t) (Nat.choose_succ_succ' n 1)
  have hsmall : theta < d := by omega
  obtain ⟨ops, hweight⟩ := exists_signedPointTensorOperations_weight_eq_multiple_gcd
    pi d mu zD zH hD hH theta hmultiple
  exact ⟨theta, ops, hweight, hpos, hprimeTheta, hlow, hsmall⟩

/-- In the genuine n=2 A(ii) degrees7/8, OWN mu is3 or6. Both SAME cycles
therefore give a literal weight4 word. This does not include degree4 itself. -/
theorem coray_case_Aii_l_two_ownDegreeCycles_choose_word
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of K)) (d mu : ℕ)
    (hd : d = 7 ∨ d = 8) (hmu : 0 < mu) (hmuThree : 3 ∣ mu) (hmuBound : mu ≤ 6)
    (zD zH : ZeroCycle X) (hD : ZeroCycle.degree pi zD = (d : ℤ))
    (hH : ZeroCycle.degree pi zH = (mu : ℤ)) :
    ∃ ops : List (closedPoints X × Bool),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = 4 ∧ 4 < d := by
  obtain ⟨lambda, hlambda⟩ := hmuThree
  have hsmall : lambda = 1 ∨ lambda = 2 := by
    rw [hlambda] at hmu hmuBound
    omega
  have hdiv : Nat.gcd d mu ∣ 4 := by
    rw [hlambda]
    rcases hsmall with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num
  obtain ⟨ops, hweight⟩ := exists_signedPointTensorOperations_weight_eq_multiple_gcd
    pi d mu zD zH hD hH 4 hdiv
  exact ⟨ops, hweight, by rcases hd with rfl | rfl <;> decide⟩

private theorem aii_leastComponent_ownDegree_three_dvd
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 2 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme C))
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (toBase C).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hdegree : (toBase C).residueDegree P.1 ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 - (toBase C).residueDegree P.1 < 3) :
    3 ∣ actualCurveCoordinateHilbertDegree C := by
  have hstep : 3 * (n + 1).choose 2 = 3 * n.choose 2 + 3 * n := by
    simpa only [Nat.reduceAdd, Nat.choose_one_right, Nat.mul_add, Nat.add_comm] using
      congrArg (fun t : ℕ => 3 * t) (Nat.choose_succ_succ' n 1)
  have hchoose : 1 ≤ n.choose 2 := Nat.choose_pos hn
  have hstrict : 3 * n < (toBase C).residueDegree P.1 := by omega
  by_contra h
  obtain ⟨R, hRcop, hRbound, hCbound⟩ :=
    selectedMinimalComponent_primeDegree_exists_originalCubic_point_bound
      p q hp hp0 n hq hnot C hmin ((Nat.prime_three.coprime_iff_not_dvd.mpr h).symm)
  exact (not_lt_of_ge (hleast R hRcop)) (hRbound.trans_lt (hCbound.trans_lt hstrict))

/-- A(ii), n>=3: actual OWN degree-d and degree-mu cycles, regularity,
degree-preserving point lift, literal word and nonzero section are all
constructed from SAME component/original-K least-degree data. -/
theorem coray_case_Aii_selectedMinimalComponent_exists_actual_word_and_nonzero_section
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 3 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme C)) (hcop : Nat.Coprime ((toBase C).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (toBase C).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hdegree : (toBase C).residueDegree P.1 ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 - (toBase C).residueDegree P.1 < 3) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P.1
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    ∃ (theta : ℕ) (ops : List (closedPoints N × Bool)),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = (theta : ℤ) ∧
        0 < theta ∧ ¬ 3 ∣ theta ∧ 1 + 3 * n * (n - 1) / 2 ≤ theta ∧
        theta < (toBase C).residueDegree P.1 ∧
        ∃ s : SchemeModuleOpenSectionsOver pi
          (schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops) ⊤,
          s ≠ 0 := by
  classical
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P.1
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase C
  let d := (toBase C).residueDegree P.1
  let mu := actualCurveCoordinateHilbertDegree C
  have hmuThree : 3 ∣ mu := aii_leastComponent_ownDegree_three_dvd
    p q hp hp0 n (by omega) hq hnot C hmin P hleast hdegree hfreedom
  have hregular := coray_case_Aii_selectedMinimalComponent_originalClosedPoint_isRegularLocalRing
    p q hp hp0 n (by omega) hq hnot C hmin hmuThree P hcop hdegree hfreedom
  obtain ⟨Q, _hQP, _hQiso, _hRelative, hGround⟩ :=
    selectedMinimalComponent_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
      p q hp hp0 n hq hnot C hmin P hregular
  obtain ⟨zH, hHnat, hmuBound⟩ := selectedMinimalComponent_genericNormalization_exists_own_degree_cycle
    p q hp hp0 n hq hnot C hmin
  have hmuPos : 0 < mu :=
    (selectedProjectiveMinimalComponent_hilbertDegree_pos_bound_and_eventualIncrement_anyField
      p q hp hp0 n hq hnot C hmin).1
  let zD : EffectiveZeroCycle N := Finsupp.single Q 1
  have hDnat : EffectiveZeroCycle.degree pi zD = d := by
    change (Finsupp.single Q 1).sum (fun R c => c * pi.residueDegree R.1) = d
    rw [Finsupp.sum_single_index (by simp)]
    exact (one_mul _).trans hGround
  have hD : ZeroCycle.degree pi zD.toZeroCycle = (d : ℤ) := by
    rw [EffectiveZeroCycle.degree_toZeroCycle, hDnat]
  have hH : ZeroCycle.degree pi zH.toZeroCycle = (mu : ℤ) := by
    rw [EffectiveZeroCycle.degree_toZeroCycle, hHnat]
  have hd : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    have hnotDiv : ¬ 3 ∣ d := Nat.prime_three.coprime_iff_not_dvd.mp hcop.symm
    apply hnotDiv
    rw [hz]
    exact dvd_zero 3
  obtain ⟨theta, ops, hWeight, hPos, hPrime, hLow, hHigh⟩ :=
    coray_case_Aii_ownDegreeCycles_choose_word pi n d mu hn hd
      (Nat.prime_three.coprime_iff_not_dvd.mp hcop.symm) hmuPos hmuThree hmuBound
      hdegree hfreedom zD.toZeroCycle zH.toZeroCycle hD hH
  have hBound : 1 + 3 * n * (n - 1) / 2 ≤ theta := by
    rw [← coray_choose_genus_eq_euler_bound n]
    exact hLow
  have hWindow : ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
      schemeModuleSignedClosedPointTensorWeightSum pi ops +
        (Module.finrank K (SchemeModuleGlobalSectionsOver (toBase C)
          (genericNormalizationQuotientSheaf X)) : ℤ) := by
    rw [hWeight]
    omega
  obtain ⟨s, hs⟩ :=
    selectedMinimalComponent_genericNormalization_signedWord_exists_nonzero_section_of_weight_add_defect_ge_bound
      p q hp hp0 n (by omega) hq hnot C hmin P.1 ops hWindow
  exact ⟨theta, ops, hWeight, hPos, hPrime, hBound, hHigh, s, hs⟩

/-- The actual n=2 component A(ii) caller uses OWN mu=3 or6 to construct
weight4 and a nonzero SAME-N section for degree7/8. Degree4 is not included. -/
theorem coray_case_Aii_l_two_selectedMinimalComponent_exists_actual_word_and_nonzero_section
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hq : q.IsHomogeneous 2)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme C))
    (hd : (toBase C).residueDegree P.1 = 7 ∨ (toBase C).residueDegree P.1 = 8)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (toBase C).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P.1
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    ∃ ops : List (closedPoints N × Bool),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = 4 ∧
        4 < (toBase C).residueDegree P.1 ∧
        ∃ s : SchemeModuleOpenSectionsOver pi
          (schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops) ⊤,
          s ≠ 0 := by
  classical
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P.1
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase C
  let d := (toBase C).residueDegree P.1
  let mu := actualCurveCoordinateHilbertDegree C
  have hdcases : d = 7 ∨ d = 8 := hd
  have hUpper : (toBase C).residueDegree P.1 ≤ 3 * (2 + 1).choose 2 := by
    change d ≤ 9
    omega
  have hFreedom : 3 * (2 + 1).choose 2 - (toBase C).residueDegree P.1 < 3 := by
    change 9 - d < 3
    omega
  have hCop : Nat.Coprime ((toBase C).residueDegree P.1) 3 := by
    rcases hd with h | h <;> rw [h] <;> decide
  have hmuThree : 3 ∣ mu := aii_leastComponent_ownDegree_three_dvd
    p q hp hp0 2 (by decide) hq hnot C hmin P hleast hUpper hFreedom
  have hregular := coray_case_Aii_selectedMinimalComponent_originalClosedPoint_isRegularLocalRing
    p q hp hp0 2 (by decide) hq hnot C hmin hmuThree P hCop hUpper hFreedom
  obtain ⟨Q, _hQP, _hQiso, _hRelative, hGround⟩ :=
    selectedMinimalComponent_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
      p q hp hp0 2 hq hnot C hmin P hregular
  obtain ⟨zH, hHnat, hmuBound⟩ := selectedMinimalComponent_genericNormalization_exists_own_degree_cycle
    p q hp hp0 2 hq hnot C hmin
  have hmuPos : 0 < mu :=
    (selectedProjectiveMinimalComponent_hilbertDegree_pos_bound_and_eventualIncrement_anyField
      p q hp hp0 2 hq hnot C hmin).1
  let zD : EffectiveZeroCycle N := Finsupp.single Q 1
  have hDnat : EffectiveZeroCycle.degree pi zD = d := by
    change (Finsupp.single Q 1).sum (fun R c => c * pi.residueDegree R.1) = d
    rw [Finsupp.sum_single_index (by simp)]
    exact (one_mul _).trans hGround
  have hD : ZeroCycle.degree pi zD.toZeroCycle = (d : ℤ) := by
    rw [EffectiveZeroCycle.degree_toZeroCycle, hDnat]
  have hH : ZeroCycle.degree pi zH.toZeroCycle = (mu : ℤ) := by
    rw [EffectiveZeroCycle.degree_toZeroCycle, hHnat]
  obtain ⟨ops, hWeight, hHigh⟩ := coray_case_Aii_l_two_ownDegreeCycles_choose_word
    pi d mu hdcases hmuPos hmuThree hmuBound zD.toZeroCycle zH.toZeroCycle hD hH
  have hWindow : ((1 + 3 * 2 * (2 - 1) / 2 : ℕ) : ℤ) ≤
      schemeModuleSignedClosedPointTensorWeightSum pi ops +
        (Module.finrank K (SchemeModuleGlobalSectionsOver (toBase C)
          (genericNormalizationQuotientSheaf X)) : ℤ) := by
    rw [hWeight]
    omega
  obtain ⟨s, hs⟩ :=
    selectedMinimalComponent_genericNormalization_signedWord_exists_nonzero_section_of_weight_add_defect_ge_bound
      p q hp hp0 2 (by decide) hq hnot C hmin P.1 ops hWindow
  exact ⟨ops, hWeight, hHigh, s, hs⟩

/-- Literal selected-q A(ii) is impossible through a least-degree original
cubic point, n>=2, including every actual integral/reducible/nonreduced branch.
The SAME-P component, its regular lift, own cycles, word/section, native
length cycle and smaller original point are constructed internally. -/
theorem coray_case_Aii_selectedCurve_through_least_originalCubic_point_false
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 2 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hPcurve : P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq))
    (hdegree : (hypersurfaceToBase p hp).residueDegree P.1 ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 - (hypersurfaceToBase p hp).residueDegree P.1 < 3) : False := by
  obtain ⟨PX, _hPXpoint, _hPXiso, hPXdegree⟩ :=
    selectedCurve_originalClosedPoint_of_originalPoint_mem_image p q hp n hq P hPcurve
  obtain ⟨C, _hIC, hmin, _hprime, Q, _hQpoint, _hQiso, hQdegree⟩ :=
    homogeneousProjective_originalClosedPoint_exists_minimalComponent
      (projectiveIntersectionIdeal p q hp hq) PX
  have hGround : (toBase C).residueDegree Q.1 = (hypersurfaceToBase p hp).residueDegree P.1 :=
    hQdegree.trans hPXdegree
  have hQcop : Nat.Coprime ((toBase C).residueDegree Q.1) 3 := hGround.symm ▸ hPcop
  have hQleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (toBase C).residueDegree Q.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1 :=
    hGround.symm ▸ hleast
  have hQupper : (toBase C).residueDegree Q.1 ≤ 3 * (n + 1).choose 2 := hGround.symm ▸ hdegree
  have hQfreedom : 3 * (n + 1).choose 2 - (toBase C).residueDegree Q.1 < 3 := hGround.symm ▸ hfreedom
  by_cases hnTwo : n = 2
  · subst n
    have hNotNine : (toBase C).residueDegree Q.1 ≠ 9 := by
      intro h
      have hNot := Nat.prime_three.coprime_iff_not_dvd.mp hQcop.symm
      rw [h] at hNot
      exact hNot (by decide)
    have hDegrees : (toBase C).residueDegree Q.1 = 7 ∨ (toBase C).residueDegree Q.1 = 8 := by
      change (toBase C).residueDegree Q.1 ≤ 9 at hQupper
      change 9 - (toBase C).residueDegree Q.1 < 3 at hQfreedom
      omega
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime Q.1
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    obtain ⟨ops, hWeight, hHigh, s, hs⟩ :=
      coray_case_Aii_l_two_selectedMinimalComponent_exists_actual_word_and_nonzero_section
        p q hp hp0 hq hnot C hmin Q hDegrees hQleast
    have hWeightNat : schemeModuleSignedClosedPointTensorWeightSum pi ops = ((4 : ℕ) : ℤ) := hWeight
    obtain ⟨R, hRcop, hRbound⟩ := selectedMinimalComponent_ownWordSection_originalCubic_imagePoint_degree_le
      p q hp hp0 2 hq hnot C hmin Q.1 ops 4 hWeightNat (by decide) s hs
    have hSmall : (hypersurfaceToBase p hp).residueDegree R.1 < (hypersurfaceToBase p hp).residueDegree P.1 :=
      (hRbound.trans_lt hHigh).trans_eq hGround
    exact (not_lt_of_ge (hleast R hRcop)) hSmall
  · letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime Q.1
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    obtain ⟨theta, ops, hWeight, _hPos, hPrime, _hLow, hHigh, s, hs⟩ :=
      coray_case_Aii_selectedMinimalComponent_exists_actual_word_and_nonzero_section
        p q hp hp0 n (by omega) hq hnot C hmin Q hQcop hQleast hQupper hQfreedom
    obtain ⟨R, hRcop, hRbound⟩ := selectedMinimalComponent_ownWordSection_originalCubic_imagePoint_degree_le
      p q hp hp0 n hq hnot C hmin Q.1 ops theta hWeight hPrime s hs
    have hSmall : (hypersurfaceToBase p hp).residueDegree R.1 < (hypersurfaceToBase p hp).residueDegree P.1 :=
      (hRbound.trans_lt hHigh).trans_eq hGround
    exact (not_lt_of_ge (hleast R hRcop)) hSmall

end PfaffianDescent.Coray

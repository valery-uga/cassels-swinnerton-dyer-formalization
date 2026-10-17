import PfaffianDescent.CorayIntegralAiiRegularPoint
import PfaffianDescent.CorayOriginalRegularClosedPointNormalizationLift
import PfaffianDescent.CorayActualNormalizationLinearSectionCycle
import PfaffianDescent.CorayEffectiveCycleSignedPointTensorOperations
import PfaffianDescent.CorayNormalizationSignedPointTensorEulerPositivity
import PfaffianDescent.CorayGenericNormalizationOriginalCubicProperMap
import PfaffianDescent.CorayNormalizationNonzeroSignedWordCokernelCycleDegree
import PfaffianDescent.CorayEffectiveCyclePointBound
import PfaffianDescent.CoraySelectedCurveOriginalPointIncidenceLift
import PfaffianDescent.CorayMinimalPointSelection


/-! Source-only genuine integral whole-intersection A(ii) cycle/word callers.
The actual original point regularity is proved internally. Actual nonzero
section positivity retains/cancels the full constants rank via base Euler. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The integral A(ii) degree window constructs the OWN normalization lift
with native residue preservation and its OWN original-K degree-3n hyperplane
cycle. No regularity, lift, residue-one, cycle or geometric-integrality premise. -/
theorem coray_case_Aii_integral_originalPoint_exists_ownLift_and_hyperplaneCycle
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 2 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hcop : Nat.Coprime ((toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) 3)
    (hdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ≤
      3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 -
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 < 3) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∃ Q : closedPoints N,
      nu Q.1 = P.1 ∧ IsIso (nu.residueFieldMap Q.1) ∧
      nu.residueDegree Q.1 = 1 ∧ pi.residueDegree Q.1 = (toBase I).residueDegree P.1 ∧
      ∃ zH : EffectiveZeroCycle N, EffectiveZeroCycle.degree pi zH = 3 * n := by
  classical
  dsimp only
  have hregular := coray_case_Aii_integral_originalClosedPoint_isRegularLocalRing
    p q hp hp0 n hlarge hq hnot P hcop hdegree hfreedom
  obtain ⟨Q, hQpoint, hQiso, hQrelative, hQground⟩ :=
    projectiveIntersection_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
      p q hp hp0 n hq hnot P hregular
  obtain ⟨zH, hHdegree⟩ :=
    projectiveIntersection_genericNormalization_exists_linearSection_cycle_degree_three_mul
      p q hp hp0 n hq hnot
  exact ⟨Q, hQpoint, hQiso, hQrelative, hQground, zH, hHdegree⟩

/-- Actual integral A(ii), n>=3, constructs a positive prime-to-three
weight below the original point degree and a nonzero section of the SAME
actual signed tensor word. Every cycle and regularity input is derived. -/
theorem coray_case_Aii_integral_originalPoint_exists_actual_word_and_nonzero_section
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 3 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hprime : ¬ 3 ∣ (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1)
    (hdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ≤
      3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 -
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 < 3) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∃ (theta : ℕ) (ops : List (closedPoints N × Bool)),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = (theta : ℤ) ∧
      0 < theta ∧ ¬ 3 ∣ theta ∧ 1 + 3 * n * (n - 1) / 2 ≤ theta ∧
      theta < (toBase I).residueDegree P.1 ∧
      ∃ s : SchemeModuleOpenSectionsOver pi
        (schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops) ⊤,
        s ≠ 0 := by
  classical
  intro I X N nu pi
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let d := (toBase I).residueDegree P.1
  have hn : 0 < n := by omega
  obtain ⟨theta0, _hpos0, _hdiv0, _hprime0, hlow0, hhigh0⟩ :=
    coray_case_Aii_degree_selection n d (3 * n.choose 2 + 1) 1 hlarge
      (by decide) (by decide) (one_dvd _) le_rfl hdegree hfreedom
  have hstrict : 1 + 3 * n * (n - 1) / 2 < d := by
    rw [← coray_choose_genus_eq_euler_bound n]
    exact hlow0.trans_lt hhigh0
  obtain ⟨Q, _hQpoint, _hQiso, _hQrelative, hQground, zH, hHnat⟩ :=
    coray_case_Aii_integral_originalPoint_exists_ownLift_and_hyperplaneCycle
      p q hp hp0 n (by omega) hq hnot P
        ((Nat.prime_three.coprime_iff_not_dvd.mpr hprime).symm) hdegree hfreedom
  let zD : EffectiveZeroCycle N := Finsupp.single Q 1
  have hDnat : EffectiveZeroCycle.degree pi zD = d := by
    change (Finsupp.single Q 1).sum (fun R c => c * pi.residueDegree R.1) = d
    rw [Finsupp.sum_single_index (by simp)]
    exact (one_mul _).trans hQground
  have hD : ZeroCycle.degree pi zD.toZeroCycle = (d : ℤ) := by
    rw [EffectiveZeroCycle.degree_toZeroCycle, hDnat]
  have hH : ZeroCycle.degree pi zH.toZeroCycle = ((3 * n : ℕ) : ℤ) := by
    rw [EffectiveZeroCycle.degree_toZeroCycle, hHnat]
  have hd : 0 < d := (Nat.zero_le _).trans_lt hstrict
  obtain ⟨theta, ops, hweight, hpos, hprimeTheta, hlow, hhigh⟩ :=
    coray_case_Aii_normalizationCycles_choose_word pi n d hlarge hd hprime hdegree hfreedom
      zD.toZeroCycle zH.toZeroCycle hD hH
  have hbound : 1 + 3 * n * (n - 1) / 2 ≤ theta := by
    rw [← coray_choose_genus_eq_euler_bound n]
    exact hlow
  have hwindow : ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
      schemeModuleSignedClosedPointTensorWeightSum pi ops := by
    rw [hweight]
    exact_mod_cast hbound
  obtain ⟨s, hs⟩ :=
    projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzero_topSection_of_weight_ge_bound
      p q hp hp0 n hn hq hnot ops hwindow
  exact ⟨theta, ops, hweight, hpos, hprimeTheta, hbound, hhigh, s, hs⟩

/-- Actual integral A(ii), n=2 and degree7/8, constructs an actual
weight4 word and a nonzero section. Regularity and both native normalization
cycles are constructed internally from the original degree conditions. -/
theorem coray_case_Aii_degree_seven_eight_integral_originalPoint_exists_actual_word_and_nonzero_section
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hq : q.IsHomogeneous 2)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hdegrees : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 = 7 ∨
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 = 8) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∃ ops : List (closedPoints N × Bool),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = 4 ∧
      4 < (toBase I).residueDegree P.1 ∧
      ∃ s : SchemeModuleOpenSectionsOver pi
        (schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops) ⊤,
        s ≠ 0 := by
  classical
  intro I X N nu pi
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let d := (toBase I).residueDegree P.1
  have hd : d = 7 ∨ d = 8 := hdegrees
  have hstrict : 1 + 3 * 2 * (2 - 1) / 2 < d := by
    change 4 < d
    omega
  obtain ⟨Q, _hQpoint, _hQiso, _hQrelative, hQground, zH, hHnat⟩ :=
    coray_case_Aii_integral_originalPoint_exists_ownLift_and_hyperplaneCycle
      p q hp hp0 2 (by decide) hq hnot P
        (by rcases hd with h | h <;> change Nat.Coprime d 3 <;> rw [h] <;> decide)
        (by change d ≤ 9; omega) (by change 9 - d < 3; omega)
  let zD : EffectiveZeroCycle N := Finsupp.single Q 1
  have hDnat : EffectiveZeroCycle.degree pi zD = d := by
    change (Finsupp.single Q 1).sum (fun R c => c * pi.residueDegree R.1) = d
    rw [Finsupp.sum_single_index (by simp)]
    exact (one_mul _).trans hQground
  have hD : ZeroCycle.degree pi zD.toZeroCycle = (d : ℤ) := by
    rw [EffectiveZeroCycle.degree_toZeroCycle, hDnat]
  have hH : ZeroCycle.degree pi zH.toZeroCycle = 6 := by
    rw [EffectiveZeroCycle.degree_toZeroCycle, hHnat]
    rfl
  obtain ⟨ops, hweight, hhigh⟩ :=
    coray_case_Aii_l_two_normalizationCycles_choose_word pi d hd zD.toZeroCycle zH.toZeroCycle hD hH
  have hwindow : ((1 + 3 * 2 * (2 - 1) / 2 : ℕ) : ℤ) ≤
      schemeModuleSignedClosedPointTensorWeightSum pi ops := by
    rw [hweight]
    decide
  obtain ⟨s, hs⟩ :=
    projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzero_topSection_of_weight_ge_bound
      p q hp hp0 2 (by decide) hq hnot ops hwindow
  exact ⟨ops, hweight, hhigh, s, hs⟩

end PfaffianDescent.Coray

/-! Source-only integral A(ii) actual smaller ORIGINAL cubic points.
Full original constants and full residue degrees remain in the length cycle. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual nonzero word section constructs its OWN native-length
cycle, then a prime-to-three original cubic point of degree at most its word
weight. No desired cycle or degree conclusion is an input. -/
theorem integralOwnWordSection_originalCubic_imagePoint_degree_le
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∀ (ops : List (closedPoints N × Bool)) (theta : ℕ),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = (theta : ℤ) →
      ¬ 3 ∣ theta →
      let W := schemeModuleIteratedSignedClosedPointTensor
        (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ s : W.val.obj (op ⊤), s ≠ 0 →
        ∃ R : closedPoints (hypersurface p hp),
          Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
            (hypersurfaceToBase p hp).residueDegree R.1 ≤ theta := by
  classical
  intro I X N nu pi ops theta hweight hprime W s hs
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let Q := cokernel (schemeModuleTopSectionHom W s)
  let C := schemeModuleStalkSupport Q
  obtain ⟨hC, hpoints, hcycleDegree⟩ :=
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_lengthCycle_degree_eq_weight
      p q hp hp0 n hn hq hnot ops s hs
  let z : EffectiveZeroCycle N := schemeModuleFiniteClosedSupportLengthCycle Q C hC hpoints
  have hdegreeInt : (EffectiveZeroCycle.degree pi z : ℤ) = (theta : ℤ) :=
    hcycleDegree.trans hweight
  have hdegree : EffectiveZeroCycle.degree pi z = theta := by exact_mod_cast hdegreeInt
  let i := cubicSecondEquationCurveImmersion p q hp n hq
  let rho := nu ≫ i
  obtain ⟨hfinite, _hproper, hbase⟩ :=
    projectiveIntersection_genericNormalization_to_originalCubic_finite_proper_and_toBase p q hp n hq
  letI : IsFinite rho := hfinite
  have hground : rho ≫ hypersurfaceToBase p hp = pi := hbase
  have hz : EffectiveZeroCycle.degree (rho ≫ hypersurfaceToBase p hp) z = theta := by
    rw [hground]
    exact hdegree
  have hcop : Nat.Coprime theta 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr hprime).symm
  have hcycleCop : Nat.Coprime (EffectiveZeroCycle.degree (rho ≫ hypersurfaceToBase p hp) z) 3 := by
    rw [hz]
    exact hcop
  obtain ⟨R_N, hRcop, hRbound⟩ := proper_effectiveCycle_coprime_degree_has_bounded_imagePoint
    rho (hypersurfaceToBase p hp) z hcycleCop
  exact ⟨universallyClosedPointMap rho R_N, hRcop, hRbound.trans_eq hz⟩

/-- Actual integral A(ii), n>=3, constructs a smaller prime-to-three
closed point on the SAME original cubic, from actual original-point inputs. -/
theorem coray_case_Aii_integral_originalPoint_exists_smaller_originalCubic_closedPoint
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 3 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hprime : ¬ 3 ∣ (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1)
    (hdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ≤
      3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 -
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 < 3) :
    ∃ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 <
          (hypersurfaceToBase p hp).residueDegree
            (cubicSecondEquationCurveImmersion p q hp n hq P.1) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  obtain ⟨theta, ops, hweight, _hpos, hthetaPrime, _hlow, hhigh, s, hs⟩ :=
    coray_case_Aii_integral_originalPoint_exists_actual_word_and_nonzero_section
      p q hp hp0 n hlarge hq hnot P hprime hdegree hfreedom
  obtain ⟨R, hRcop, hRbound⟩ := integralOwnWordSection_originalCubic_imagePoint_degree_le
    p q hp hp0 n (by omega) hq hnot ops theta hweight hthetaPrime s hs
  have hPground := projectiveIntersection_originalClosedPoint_degree_eq_originalCubicImage_degree
    p q hp n hq P
  exact ⟨R, hRcop, (hRbound.trans_lt hhigh).trans_eq hPground⟩

/-- Actual n=2 degree7/8 A(ii) produces an ORIGINAL cubic point of degree
at most four and prime to three, strictly below the actual original image P. -/
theorem coray_case_Aii_degree_seven_eight_integral_originalPoint_exists_smaller_originalCubic_closedPoint
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hq : q.IsHomogeneous 2)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hdegrees : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 = 7 ∨
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 = 8) :
    ∃ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 ≤ 4 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 <
          (hypersurfaceToBase p hp).residueDegree
            (cubicSecondEquationCurveImmersion p q hp 2 hq P.1) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  obtain ⟨ops, hweight, hhigh, s, hs⟩ :=
    coray_case_Aii_degree_seven_eight_integral_originalPoint_exists_actual_word_and_nonzero_section
      p q hp hp0 hq hnot P hdegrees
  obtain ⟨R, hRcop, hRbound⟩ := integralOwnWordSection_originalCubic_imagePoint_degree_le
    p q hp hp0 2 (by decide) hq hnot ops 4 hweight (by decide) s hs
  have hPground := projectiveIntersection_originalClosedPoint_degree_eq_originalCubicImage_degree
    p q hp 2 hq P
  exact ⟨R, hRcop, hRbound, (hRbound.trans_lt hhigh).trans_eq hPground⟩

end PfaffianDescent.Coray

/-! Actual least-degree contradictions on the SAME ORIGINAL cubic. The
selected q's actual integrality and original-point incidence remain explicit.
The actual closed curve lift, its residue preservation, the signed word,
nonzero section, own native-length cycle and smaller original point are
all constructed. No smaller point/cycle/word/section premise. SOURCE ONLY /
UNVERIFIED. Integrality selection and the reducible branch remain separate geometry. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine integral selected curve through the SAME least prime-to-three
ORIGINAL cubic point cannot lie in A(ii), n≥3, with the natural original
degree/freedom constraints. The smaller point is actually constructed. -/
theorem coray_case_Aii_integral_selectedCurve_through_least_originalCubic_point_false
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 3 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤
          (hypersurfaceToBase p hp).residueDegree R.1)
    (hPcurve : P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq))
    (hdegree : (hypersurfaceToBase p hp).residueDegree P.1 ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 -
      (hypersurfaceToBase p hp).residueDegree P.1 < 3) : False := by
  obtain ⟨Q, hpoint, _hresidue, hQdegree⟩ :=
    selectedCurve_originalClosedPoint_of_originalPoint_mem_image p q hp n hq P hPcurve
  have hprimeQ : ¬ 3 ∣ (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 := by
    rw [hQdegree]
    exact Nat.prime_three.coprime_iff_not_dvd.mp hPcop.symm
  have hdegreeQ : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 ≤
      3 * (n + 1).choose 2 := by
    rw [hQdegree]
    exact hdegree
  have hfreedomQ : 3 * (n + 1).choose 2 -
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 < 3 := by
    rw [hQdegree]
    exact hfreedom
  obtain ⟨R, hRcop, hRsmall⟩ :=
    coray_case_Aii_integral_originalPoint_exists_smaller_originalCubic_closedPoint
      p q hp hp0 n hlarge hq hnot Q hprimeQ hdegreeQ hfreedomQ
  rw [hpoint] at hRsmall
  exact (not_lt_of_ge (hleast R hRcop)) hRsmall

/-- The SAME ORIGINAL cubic least-degree premise also excludes the actual
integral n=2 A(ii) cases degree7/8. The actual smaller point has degree at most4;
the contradiction uses only its derived coprimality and strict inequality. -/
theorem coray_case_Aii_degree_seven_eight_integral_selectedCurve_through_least_originalCubic_point_false
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hq : q.IsHomogeneous 2)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (hypersurface p hp))
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤
          (hypersurfaceToBase p hp).residueDegree R.1)
    (hPcurve : P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp 2 hq))
    (hdegrees : (hypersurfaceToBase p hp).residueDegree P.1 = 7 ∨
      (hypersurfaceToBase p hp).residueDegree P.1 = 8) : False := by
  obtain ⟨Q, hpoint, _hresidue, hQdegree⟩ :=
    selectedCurve_originalClosedPoint_of_originalPoint_mem_image p q hp 2 hq P hPcurve
  have hdegreesQ : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 = 7 ∨
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 = 8 := by
    rw [hQdegree]
    exact hdegrees
  obtain ⟨R, hRcop, _hRfour, hRsmall⟩ :=
    coray_case_Aii_degree_seven_eight_integral_originalPoint_exists_smaller_originalCubic_closedPoint
      p q hp hp0 hq hnot Q hdegreesQ
  rw [hpoint] at hRsmall
  exact (not_lt_of_ge (hleast R hRcop)) hRsmall

/-- The complete integral whole-intersection A(ii) branch, n>=2, is
impossible through a least-degree prime-to-three ORIGINAL cubic point.
The n=2 degree7/8 split is derived internally from the natural degree
window and coprimality. No geometric-integrality or desired-outcome input. -/
theorem coray_case_Aii_integral_selectedCurve_through_least_originalCubic_point_false_of_two_le
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 2 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤
          (hypersurfaceToBase p hp).residueDegree R.1)
    (hPcurve : P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq))
    (hdegree : (hypersurfaceToBase p hp).residueDegree P.1 ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 -
      (hypersurfaceToBase p hp).residueDegree P.1 < 3) : False := by
  by_cases hn : n = 2
  · subst n
    have hprime : ¬ 3 ∣ (hypersurfaceToBase p hp).residueDegree P.1 :=
      Nat.prime_three.coprime_iff_not_dvd.mp hPcop.symm
    have hnotNine : (hypersurfaceToBase p hp).residueDegree P.1 ≠ 9 := by
      intro heq
      apply hprime
      rw [heq]
      decide
    have hdegrees : (hypersurfaceToBase p hp).residueDegree P.1 = 7 ∨
        (hypersurfaceToBase p hp).residueDegree P.1 = 8 := by
      change (hypersurfaceToBase p hp).residueDegree P.1 ≤ 9 at hdegree
      change 9 - (hypersurfaceToBase p hp).residueDegree P.1 < 3 at hfreedom
      omega
    exact coray_case_Aii_degree_seven_eight_integral_selectedCurve_through_least_originalCubic_point_false
      p q hp hp0 hq hnot P hleast hPcurve hdegrees
  · exact coray_case_Aii_integral_selectedCurve_through_least_originalCubic_point_false
      p q hp hp0 n (by omega) hq hnot P hPcop hleast hPcurve hdegree hfreedom

end PfaffianDescent.Coray

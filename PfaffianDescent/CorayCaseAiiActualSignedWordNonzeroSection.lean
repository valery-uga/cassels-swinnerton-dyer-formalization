import PfaffianDescent.CorayEffectiveCycleSignedPointTensorOperations
import PfaffianDescent.CorayStrictOriginalPointNormalizationCycles
import PfaffianDescent.CorayNormalizationSignedPointTensorEulerPositivity

/-! Actual branch-A(ii) signed-word selection and nonzero section. The
original P and genuine GI selected-curve branch are inputs, not its regularity,
a normalization lift, either normalization cycle, desired theta/weight, ops,
or section. Natural numerical freedom selects the strict point regularity
case, actual geometry constructs both degrees, and actual cycle encoding
selects ops with full ORIGINAL-K residue weights. Pending geometry and
historical word-encoding imports remain explicit. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nat_le_int_cast (a b : ℕ) (h : a ≤ b) : (a : ℤ) ≤ (b : ℤ) := by
  omega

/-- Actual A(ii), n>=3: natural original degree/freedom assumptions produce
a positive prime-to-three theta<deg(P), an ACTUAL word of exactly that weight,
and a NONZERO section of the SAME literal signed tensor word. The original
P's regularity and both genuine normalization cycles are constructed internally.
GI is the source's genuine branch hypothesis, not a claimed interpolation output. -/
theorem coray_case_Aii_geometricallyIntegral_originalPoint_exists_actual_word_and_nonzero_section
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 3 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hprime : ¬ 3 ∣ (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1)
    (hdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ≤
      3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 -
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 < 3) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
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
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
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
    projectiveIntersection_geometricallyIntegral_strictOriginalPoint_exists_ownLift_and_hyperplaneCycle
      p q hp hp0 n hn hq hnot P hstrict
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
    exact nat_le_int_cast _ _ hbound
  obtain ⟨s, hs⟩ :=
    projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzero_topSection_of_weight_ge_bound
      p q hp hp0 n hn hq hnot ops hwindow
  exact ⟨theta, ops, hweight, hpos, hprimeTheta, hbound, hhigh, s, hs⟩

/-- Actual A(ii), n=2 and original degree7/8: internally generated own
normalization cycles yield actual weight4 and a NONZERO section. These small
cases do not fit the n>=3 arithmetic selector; no desired weight is an input. -/
theorem coray_case_Aii_degree_seven_eight_geometricallyIntegral_originalPoint_exists_actual_word_and_nonzero_section
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hq : q.IsHomogeneous 2)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hdegrees : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 = 7 ∨
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 = 8) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
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
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let d := (toBase I).residueDegree P.1
  have hd : d = 7 ∨ d = 8 := hdegrees
  have hstrict : 1 + 3 * 2 * (2 - 1) / 2 < d := by
    change 4 < d
    omega
  obtain ⟨Q, _hQpoint, _hQiso, _hQrelative, hQground, zH, hHnat⟩ :=
    projectiveIntersection_geometricallyIntegral_strictOriginalPoint_exists_ownLift_and_hyperplaneCycle
      p q hp hp0 2 (by decide) hq hnot P hstrict
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

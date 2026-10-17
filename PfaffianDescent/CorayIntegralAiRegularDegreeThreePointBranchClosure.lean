import PfaffianDescent.CorayIntegralAiRegularDegreeThreePointRegularity
import PfaffianDescent.CorayNormalizationSignedPointTensorEulerPositivity
import PfaffianDescent.CorayIntegralAiiBranchClosure
import AllCharacteristics.EffectiveCycleToZeroCycle

/-! Source-only conditional downstream Ai glue. Literal SAME original curve,
normalization and scalar actions are retained. The only geometric input beyond
the actual integral curve/strict point is an ACTUAL regular degree-three point
of that curve. The natural surface selector is still missing. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal singleton with coefficient one keeps the actual full degree. -/
private theorem actualSingletonEffectiveZeroCycle_signedDegree001
    {X Y : Scheme.{u}} (pi : X ⟶ Y) (P : closedPoints X) :
    ZeroCycle.degree pi
      (EffectiveZeroCycle.toZeroCycle (Finsupp.single P 1 : EffectiveZeroCycle X)) =
      (pi.residueDegree P.1 : ℤ) := by
  rw [EffectiveZeroCycle.degree_toZeroCycle]
  congr 1
  change (Finsupp.single P (1 : ℕ)).sum
    (fun R c => c * pi.residueDegree R.1) = pi.residueDegree P.1
  rw [Finsupp.sum_single_index (by simp)]
  exact one_mul _

/-- A genuine regular degree-three SAME-curve point constructs both actual
normalization singleton cycles, hence literal Ai word weight G_n and its actual
nonzero section. P regularity and all degree-preserving lifts are derived.
No word, section, normalization cycle, GI or rank-one premise. -/
theorem coray_case_Ai_integral_originalPoint_exists_actual_word_and_nonzero_section_of_regular_degreeThreePoint001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P A : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPcop : Nat.Coprime ((toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) 3)
    (hstrict : 3 * n.choose 2 + 1 <
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1)
    (hAdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree A.1 = 3)
    (hAregular : IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk A.1)) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∃ ops : List (closedPoints N × Bool),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = ((3 * n.choose 2 + 1 : ℕ) : ℤ) ∧
      ¬ 3 ∣ 3 * n.choose 2 + 1 ∧
      3 * n.choose 2 + 1 < (toBase I).residueDegree P.1 ∧
      ∃ s : SchemeModuleOpenSectionsOver pi
        (schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops) ⊤,
        s ≠ 0 := by
  classical
  intro I X N nu pi
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  have hPregular :=
    projectiveIntersection_integral_originalClosedPoint_isRegularLocalRing_of_degree_gt_of_regular_degreeThreePoint001
      p q hp hp0 n hn hq hnot P A hPcop hstrict hAdegree hAregular
  obtain ⟨PN, _hPNpoint, _hPNiso, _hPNrelative, hPNdegree⟩ :=
    projectiveIntersection_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
      p q hp hp0 n hq hnot P hPregular
  obtain ⟨AN, _hANpoint, _hANiso, _hANrelative, hANdegree⟩ :=
    projectiveIntersection_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
      p q hp hp0 n hq hnot A hAregular
  let zD : EffectiveZeroCycle N := Finsupp.single PN 1
  let zThree : EffectiveZeroCycle N := Finsupp.single AN 1
  have hD : ZeroCycle.degree pi zD.toZeroCycle = ((toBase I).residueDegree P.1 : ℤ) :=
    (actualSingletonEffectiveZeroCycle_signedDegree001 pi PN).trans
      (congrArg (fun d : ℕ => (d : ℤ)) hPNdegree)
  have hThree : ZeroCycle.degree pi zThree.toZeroCycle = 3 := by
    have h := (actualSingletonEffectiveZeroCycle_signedDegree001 pi AN).trans
      (congrArg (fun d : ℕ => (d : ℤ)) (hANdegree.trans hAdegree))
    exact h
  have hPprime : ¬ 3 ∣ (toBase I).residueDegree P.1 :=
    Nat.prime_three.coprime_iff_not_dvd.mp hPcop.symm
  obtain ⟨ops, hweight, hprime, hsmall⟩ := coray_case_Ai_normalizationCycles_choose_word
    pi n ((toBase I).residueDegree P.1) hPprime hstrict
      zD.toZeroCycle zThree.toZeroCycle hD hThree
  have hwindow : ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
      schemeModuleSignedClosedPointTensorWeightSum pi ops := by
    rw [hweight]
    exact_mod_cast (coray_choose_genus_eq_euler_bound n).symm.le
  obtain ⟨s, hs⟩ :=
    projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzero_topSection_of_weight_ge_bound
      p q hp hp0 n hn hq hnot ops hwindow
  exact ⟨ops, hweight, hprime, hsmall, s, hs⟩

/-- The SAME genuinely regular degree-three point gives an actual original
cubic point of full prime-to-three degree at most G_n, strictly below the full
original degree of the immersion image of P. Actual section/cycle/pushforward
construction is reused from the accepted generic public own-word consumer.
This is conditional downstream glue, not the missing natural selector. -/
theorem coray_case_Ai_integral_originalPoint_exists_smaller_originalCubic_closedPoint_of_regular_degreeThreePoint001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P A : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPcop : Nat.Coprime ((toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) 3)
    (hstrict : 3 * n.choose 2 + 1 <
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1)
    (hAdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree A.1 = 3)
    (hAregular : IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk A.1)) :
    ∃ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 ≤ 3 * n.choose 2 + 1 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 <
          (hypersurfaceToBase p hp).residueDegree
            (cubicSecondEquationCurveImmersion p q hp n hq P.1) := by
  obtain ⟨ops, hweight, hprime, hsmall, s, hs⟩ :=
    coray_case_Ai_integral_originalPoint_exists_actual_word_and_nonzero_section_of_regular_degreeThreePoint001
      p q hp hp0 n hn hq hnot P A hPcop hstrict hAdegree hAregular
  obtain ⟨R, hRcop, hRbound⟩ := integralOwnWordSection_originalCubic_imagePoint_degree_le
    p q hp hp0 n hn hq hnot ops (3 * n.choose 2 + 1) hweight hprime s hs
  have hPground := projectiveIntersection_originalClosedPoint_degree_eq_originalCubicImage_degree
    p q hp n hq P
  exact ⟨R, hRcop, hRbound, (hRbound.trans_lt hsmall).trans_eq hPground⟩

end PfaffianDescent.Coray

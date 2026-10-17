import PfaffianDescent.CorayIntegralBoundaryConstants
import PfaffianDescent.CorayIntegralAiiBranchClosure
import PfaffianDescent.CorayBoundaryConstructedSingularReducedCubicCycle
import PfaffianDescent.CorayCubicPolynomialDualAnnihilatorDimension
import PfaffianDescent.CorayEffectiveCycleSignedPointTensorOperations
import PfaffianDescent.CorayActualNormalizationLinearSectionCycle
import PfaffianDescent.CorayNormalizationSignedPointTensorSharpSection

/-! Source-only integral A(iii) actual word/section/smaller original point,
then integration with the primitive SAME-q singular curve-cycle producer.
No cycle or integrality conclusion is smuggled into primitive caller inputs. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem boundary_sharp_integer_window
    (B theta delta : ℕ) (htheta : B ≤ theta + 3) (hdelta : 3 ≤ delta) :
    (B : ℤ) ≤ (theta : ℤ) + (delta : ℤ) := by
  omega

/-- Given the actual ORIGINAL curve's natural boundary singular support,
construct the actual smaller signed word and a NONZERO section. Its own
quotient gain>=3, original-P regularity, degree-preserving lift, normalization
hyperplane cycle, theta, exact weight and section are all derived. The given
singular cycle is NOT lifted. Its earlier geometric producer is separate. -/
theorem coray_case_Aiii_integral_originalPoint_and_singularCurveCycle_exists_actual_word_and_nonzero_section
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 3 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 =
      1 + 3 * n * (n - 1) / 2)
    (zB : EffectiveZeroCycle (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hred : ∀ R ∈ zB.support, zB R = 1)
    (hBdegree : EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) zB = 3)
    (hdisjoint : P ∉ zB.support)
    (hBsing : ∀ R ∈ zB.support, ¬ IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk R.1)) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    let d := (toBase I).residueDegree P.1
    ∃ (theta : ℕ) (ops : List (closedPoints N × Bool)),
      (theta = d - 3 ∨ theta = d - 2) ∧
      schemeModuleSignedClosedPointTensorWeightSum pi ops = (theta : ℤ) ∧
      0 < theta ∧ ¬ 3 ∣ theta ∧ theta < d ∧
      ∃ s : SchemeModuleOpenSectionsOver pi
        (schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops) ⊤,
        s ≠ 0 := by
  classical
  intro I X N nu pi d
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  have hn : 0 < n := by omega
  have hregular :=
    projectiveIntersection_integral_originalClosedPoint_isRegularLocalRing_at_boundary_of_singular_reducedDegreeThree
      p q hp hp0 n hlarge hq hnot P hPdegree zB hred hBdegree hdisjoint hBsing
  obtain ⟨Q, _hQpoint, _hQiso, _hQrelative, hQground⟩ :=
    projectiveIntersection_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
      p q hp hp0 n hq hnot P hregular
  obtain ⟨zH, hHnat⟩ :=
    projectiveIntersection_genericNormalization_exists_linearSection_cycle_degree_three_mul
      p q hp hp0 n hq hnot
  let zD : EffectiveZeroCycle N := Finsupp.single Q 1
  have hDnat : EffectiveZeroCycle.degree pi zD = d := by
    change (Finsupp.single Q 1).sum (fun R c => c * pi.residueDegree R.1) = d
    rw [Finsupp.sum_single_index (by simp)]
    exact (one_mul _).trans hQground
  have hPchoose : d = 3 * n.choose 2 + 1 :=
    hPdegree.trans (coray_choose_genus_eq_euler_bound n).symm
  have hD : ZeroCycle.degree pi zD.toZeroCycle = ((3 * n.choose 2 + 1 : ℕ) : ℤ) := by
    rw [EffectiveZeroCycle.degree_toZeroCycle, hDnat, hPchoose]
  have hH : ZeroCycle.degree pi zH.toZeroCycle = ((3 * n : ℕ) : ℤ) := by
    rw [EffectiveZeroCycle.degree_toZeroCycle, hHnat]
  obtain ⟨theta, ops, hcandidates, hweight, hpos, hprime, hlow, hhigh⟩ :=
    coray_case_Aiii_normalizationCycles_choose_word pi n (by omega) zD.toZeroCycle zH.toZeroCycle hD hH
  have hsum := projectiveIntersection_genericNormalization_distinct_nonregular_residueSum_le_globalDefect
    p q hp hp0 n hq hnot zB.support hBsing
  have hBsum : ∑ R ∈ zB.support, (toBase I).residueDegree R.1 = 3 := by
    calc
      ∑ R ∈ zB.support, (toBase I).residueDegree R.1 =
          ∑ R ∈ zB.support, zB R * (toBase I).residueDegree R.1 := by
        apply Finset.sum_congr rfl
        intro R hR
        rw [hred R hR, one_mul]
      _ = EffectiveZeroCycle.degree (toBase I) zB := rfl
      _ = 3 := hBdegree
  have hdelta : 3 ≤ Module.finrank K
      (SchemeModuleGlobalSectionsOver (toBase I) (genericNormalizationQuotientSheaf X)) :=
    hBsum ▸ hsum
  have hthetaBound : 1 + 3 * n * (n - 1) / 2 ≤ theta + 3 :=
    (coray_choose_genus_eq_euler_bound n) ▸ hlow
  have hwindow : ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
      schemeModuleSignedClosedPointTensorWeightSum pi ops +
        (Module.finrank K (SchemeModuleGlobalSectionsOver
          (toBase I) (genericNormalizationQuotientSheaf X)) : ℤ) := by
    rw [hweight]
    exact boundary_sharp_integer_window _ _ _ hthetaBound hdelta
  obtain ⟨s, hs⟩ :=
    projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzero_topSection_of_weight_add_quotient_ge_bound
      p q hp hp0 n hn hq hnot ops hwindow
  exact ⟨theta, ops, hPchoose.symm ▸ hcandidates, hweight, hpos, hprime,
    hPchoose.symm ▸ hhigh, s, hs⟩

/-- Integral A(iii), n>=3: internally selected word and its actual nonzero
section construct an actual smaller prime-to-three original cubic point.
The support datum is the SAME original curve singular reduced cubic cycle. -/
theorem coray_case_Aiii_integral_originalPoint_and_singularCurveCycle_exists_smaller_originalCubic_closedPoint
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 3 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 =
      1 + 3 * n * (n - 1) / 2)
    (zB : EffectiveZeroCycle (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hred : ∀ R ∈ zB.support, zB R = 1)
    (hBdegree : EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) zB = 3)
    (hdisjoint : P ∉ zB.support)
    (hBsing : ∀ R ∈ zB.support, ¬ IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk R.1)) :
    ∃ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 <
          (hypersurfaceToBase p hp).residueDegree
            (cubicSecondEquationCurveImmersion p q hp n hq P.1) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  obtain ⟨theta, ops, _hcandidates, hweight, _hpos, hthetaPrime, hhigh, s, hs⟩ :=
    coray_case_Aiii_integral_originalPoint_and_singularCurveCycle_exists_actual_word_and_nonzero_section
      p q hp hp0 n hlarge hq hnot P hPdegree zB hred hBdegree hdisjoint hBsing
  obtain ⟨R, hRcop, hRbound⟩ := integralOwnWordSection_originalCubic_imagePoint_degree_le
    p q hp hp0 n (by omega) hq hnot ops theta hweight hthetaPrime s hs
  have hPground := projectiveIntersection_originalClosedPoint_degree_eq_originalCubicImage_degree
    p q hp n hq P
  exact ⟨R, hRcop, (hRbound.trans_lt hhigh).trans_eq hPground⟩

/-- Primitive original boundary data constructs the SAME q and its SAME
singular reduced cubic curve cycle internally. Either that actual whole
intersection is nonintegral, or its integral branch constructs an actual
smaller prime-to-three point on the ORIGINAL cubic. No q, cycle, singularity,
regularity, GI, integrality certificate or smaller point is supplied. -/
theorem boundary_originalPoint_exists_selectedCurve_nonintegral_or_smaller_originalCubic_point
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (m : ℕ) (hm : 3 ≤ m)
    (hdegree : (hypersurfaceToBase p hp).residueDegree P.1 =
      (m + 3).choose 3 - m.choose 3) :
    ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous (m + 1)),
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp (m + 1) hq) ∧
      (¬ IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) ∨
        ∃ R : closedPoints (hypersurface p hp),
          Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
            (hypersurfaceToBase p hp).residueDegree R.1 <
              (hypersurfaceToBase p hp).residueDegree P.1) := by
  classical
  obtain ⟨A, q, hq, hqnot, _hAP, _hAdegree, PX, AX, zB,
      hPX, _hAX, _hPXresidue, _hAXresidue, hPXdegree, _hAXdegree,
      _hPXAX, _hzsingle, hred, hBdegree, hdisjoint, hBsing⟩ :=
    boundary_exists_selectedCurve_originalPoint_and_disjoint_singular_reducedCubic_cycle
      p hp hp0 P hPcop hno m hm hdegree
  refine ⟨q, hq, hqnot, ⟨PX.1, hPX⟩, ?_⟩
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  by_cases hIntegral : IsIntegral X
  · letI : IsIntegral X := hIntegral
    apply Or.inr
    have hcount : (m + 3).choose 3 - m.choose 3 =
        1 + 3 * (m + 1) * ((m + 1) - 1) / 2 := by
      have h := cubicPolynomialAnnihilator_choose_difference_div (m + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.add_sub_cancel] using h
    have hboundary : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree PX.1 =
        1 + 3 * (m + 1) * ((m + 1) - 1) / 2 := hPXdegree.trans (hdegree.trans hcount)
    obtain ⟨R, hRcop, hRsmall⟩ :=
      coray_case_Aiii_integral_originalPoint_and_singularCurveCycle_exists_smaller_originalCubic_closedPoint
        p q hp hp0 (m + 1) (by omega) hq hqnot PX hboundary zB hred hBdegree hdisjoint hBsing
    rw [hPX] at hRsmall
    exact ⟨R, hRcop, hRsmall⟩
  · exact Or.inl hIntegral

/-- At a least-degree prime-to-three original boundary point, the actual
primitive SAME-q cycle producer yields a selected whole intersection that
is nonintegral. This genuinely eliminates its integral A(iii) branch; it
does not assert a component classification for the remaining actual q. -/
theorem boundary_least_originalPoint_exists_nonintegral_selectedCurve
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤
          (hypersurfaceToBase p hp).residueDegree R.1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (m : ℕ) (hm : 3 ≤ m)
    (hdegree : (hypersurfaceToBase p hp).residueDegree P.1 =
      (m + 3).choose 3 - m.choose 3) :
    ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous (m + 1)),
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
        P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp (m + 1) hq) ∧
        ¬ IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq)) := by
  obtain ⟨q, hq, hqnot, hPcurve, hbranch⟩ :=
    boundary_originalPoint_exists_selectedCurve_nonintegral_or_smaller_originalCubic_point
      p hp hp0 P hPcop hno m hm hdegree
  refine ⟨q, hq, hqnot, hPcurve, ?_⟩
  rcases hbranch with hnonintegral | ⟨R, hRcop, hRsmall⟩
  · exact hnonintegral
  · exact False.elim ((not_lt_of_ge (hleast R hRcop)) hRsmall)

end PfaffianDescent.Coray

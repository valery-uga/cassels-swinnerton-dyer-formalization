import PfaffianDescent.CorayGenericNormalizationOriginalCubicProperMap
import PfaffianDescent.CorayNormalizationNonzeroSignedWordCokernelCycleDegree
import PfaffianDescent.CorayEffectiveCyclePointBound
import PfaffianDescent.CorayCaseAiiActualSignedWordNonzeroSection
import PfaffianDescent.CorayCaseAiiiActualSignedWordNonzeroSection

/-! ACTUAL smaller original-cubic point from the SAME own signed-word
section cokernel cycle. The case callers construct ops, theta and section;
L7 constructs its OWN native-length cycle, and full-residue proper
pushforward extracts an actual smaller point over ORIGINAL K. No point,
word, section, normalization cycle or desired cycle degree is supplied to
the case endpoints. Genuine GI and boundary original singular support
retain their explicit source scope. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Internal consumer of the ACTUAL selected word and section. The exact
cycle degree is DERIVED from L7; no cycle/degree premise is accepted. All
public case callers below construct its word, weight and section inputs. -/
private theorem ownWordSection_originalCubic_imagePoint_degree_le
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

/-- Actual A(ii), n≥3, produces a closed point on the ORIGINAL cubic
prime to three and strictly smaller than the ORIGINAL cubic image of P.
Own word, nonzero section and exact own cokernel cycle are all constructed. -/
theorem coray_case_Aii_geometricallyIntegral_originalPoint_exists_smaller_originalCubic_closedPoint
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
    ∃ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 <
          (hypersurfaceToBase p hp).residueDegree
            (cubicSecondEquationCurveImmersion p q hp n hq P.1) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  obtain ⟨theta, ops, hweight, _hpos, hthetaPrime, _hlow, hhigh, s, hs⟩ :=
    coray_case_Aii_geometricallyIntegral_originalPoint_exists_actual_word_and_nonzero_section
      p q hp hp0 n hlarge hq hnot P hprime hdegree hfreedom
  obtain ⟨R, hRcop, hRbound⟩ := ownWordSection_originalCubic_imagePoint_degree_le
    p q hp hp0 n (by omega) hq hnot ops theta hweight hthetaPrime s hs
  have hPground := projectiveIntersection_originalClosedPoint_degree_eq_originalCubicImage_degree
    p q hp n hq P
  exact ⟨R, hRcop, (hRbound.trans_lt hhigh).trans_eq hPground⟩

/-- Actual n=2 degree7/8 A(ii) produces an ORIGINAL cubic point of degree
at most four and prime to three, strictly below the actual original image P. -/
theorem coray_case_Aii_degree_seven_eight_geometricallyIntegral_originalPoint_exists_smaller_originalCubic_closedPoint
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hq : q.IsHomogeneous 2)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))]
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
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  obtain ⟨ops, hweight, hhigh, s, hs⟩ :=
    coray_case_Aii_degree_seven_eight_geometricallyIntegral_originalPoint_exists_actual_word_and_nonzero_section
      p q hp hp0 hq hnot P hdegrees
  obtain ⟨R, hRcop, hRbound⟩ := ownWordSection_originalCubic_imagePoint_degree_le
    p q hp hp0 2 (by decide) hq hnot ops 4 hweight (by decide) s hs
  have hPground := projectiveIntersection_originalClosedPoint_degree_eq_originalCubicImage_degree
    p q hp 2 hq P
  exact ⟨R, hRcop, hRbound, (hRbound.trans_lt hhigh).trans_eq hPground⟩

/-- Actual boundary A(iii), with its ORIGINAL singular reduced degree-three
support, produces an actual smaller prime-to-three ORIGINAL cubic point.
That singular support supplies only the defect gain; the extracted point
comes from the distinct own nonzero-section cokernel cycle. -/
theorem coray_case_Aiii_geometricallyIntegral_originalPoint_and_singularCurveCycle_exists_smaller_originalCubic_closedPoint
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 2 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))]
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
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  obtain ⟨theta, ops, _hcandidates, hweight, _hpos, hthetaPrime, hhigh, s, hs⟩ :=
    coray_case_Aiii_geometricallyIntegral_originalPoint_and_singularCurveCycle_exists_actual_word_and_nonzero_section
      p q hp hp0 n hlarge hq hnot P hPdegree zB hred hBdegree hdisjoint hBsing
  obtain ⟨R, hRcop, hRbound⟩ := ownWordSection_originalCubic_imagePoint_degree_le
    p q hp hp0 n (by omega) hq hnot ops theta hweight hthetaPrime s hs
  have hPground := projectiveIntersection_originalClosedPoint_degree_eq_originalCubicImage_degree
    p q hp n hq P
  exact ⟨R, hRcop, (hRbound.trans_lt hhigh).trans_eq hPground⟩

end PfaffianDescent.Coray

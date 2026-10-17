import PfaffianDescent.CorayEffectiveCycleSignedPointTensorOperations
import PfaffianDescent.CorayProjectiveOriginalPointBoundaryRegularity
import PfaffianDescent.CorayActualNormalizationLinearSectionCycle
import PfaffianDescent.CorayNormalizationSignedPointTensorSharpSection

/-! Actual boundary signed word from the OWN original singular degree-three
support, OWN regular-P lift, and OWN constructed normalization hyperplane
cycle. The singular auxiliary curve cycle is used ONLY for actual quotient
contribution, never as a degree-preserving normalization cycle. Original K
and full own residues are retained. Pending D3/boundary/hyperplane/encoding
prerequisites remain explicit. SOURCE ONLY / UNVERIFIED. -/
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
theorem coray_case_Aiii_geometricallyIntegral_originalPoint_and_singularCurveCycle_exists_actual_word_and_nonzero_section
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
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
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
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  have hn : 0 < n := by omega
  have hregular :=
    projectiveIntersection_geometricallyIntegral_originalClosedPoint_isRegularLocalRing_at_boundary_of_singular_reducedDegreeThree
      p q hp hp0 n hn hq hnot P hPdegree zB hred hBdegree hdisjoint hBsing
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
    coray_case_Aiii_normalizationCycles_choose_word pi n hlarge zD.toZeroCycle zH.toZeroCycle hD hH
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

end PfaffianDescent.Coray

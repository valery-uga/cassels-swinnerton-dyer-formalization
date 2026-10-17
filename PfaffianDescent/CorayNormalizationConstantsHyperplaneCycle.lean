import PfaffianDescent.CorayOwnComponentProperConstants
import PfaffianDescent.CorayActualNormalizationLinearSectionCycle
import PfaffianDescent.CoraySignedCycleWordDegreeSelection
import PfaffianDescent.CorayIntegralFullConstantsNormalizationDefectBound

/-! Source-only actual constants rank divides the OWN normalization hyperplane
cycle degree. A(ii)'s singular original point then forces a factor three in
that rank. No GI, chosen normalization lift of singular P, constants=K,
stabilizer-field identification or desired divisibility is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual proper integral global-functions field divides the degree
of every actual effective cycle, by its genuine residue embedding at EACH
closed point of this SAME scheme. -/
theorem integralProper_globalUnitSections_finrank_dvd_effectiveCycle_degree
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] (z : EffectiveZeroCycle X) :
    Module.finrank K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) ∣ EffectiveZeroCycle.degree pi z := by
  classical
  change Module.finrank K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) ∣
    ∑ P ∈ z.support, z P * pi.residueDegree P.1
  apply Finset.dvd_sum
  intro P _hP
  exact dvd_mul_of_dvd_right
    (integralProper_originalUnitSections_finrank_dvd_residueDegree pi P) (z P)


/-- Primitive original integral p/q: construct the OWN normalization's
hyperplane cycle and derive its FULL constants rank divides exactly 3*n.
No cycle or rank-divisibility premise is supplied. -/
theorem projectiveIntersection_genericNormalization_constantsRank_dvd_three_mul
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ toBase I)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) ∣ 3 * n := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsIntegral N := inferInstance
  letI : IsFinite ν := integralScheme_genericNormalization_isFinite X (toBase I)
  letI : IsProper (ν ≫ toBase I) := inferInstance
  have hCycle := projectiveIntersection_genericNormalization_exists_linearSection_cycle_degree_three_mul
    p q hp hp0 n hq hnot
  let z : EffectiveZeroCycle N := Classical.choose hCycle
  have hdegree : EffectiveZeroCycle.degree (ν ≫ toBase I) z = 3 * n := Classical.choose_spec hCycle
  have hdiv := integralProper_globalUnitSections_finrank_dvd_effectiveCycle_degree (ν ≫ toBase I) z
  exact hdegree ▸ hdiv


private theorem aii_smallConstants_contradiction (n a d : ℕ)
    (hn : 2 ≤ n) (ha : a ≤ n)
    (hlarge : d + 1 ≤ a + (3 * n.choose 2 + 1))
    (hdegree : d ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 - d < 3) : False := by
  have hstep : 3 * (n + 1).choose 2 = 3 * n.choose 2 + 3 * n := by
    rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    norm_num only at *
    omega
  omega

/-- A(ii) without GI: original P is regular OR the FULL actual normalization
constants rank is divisible by three. The OWN cycle gives a|3n; otherwise
a|n and a<=n, contradicting the genuine full-constants singularity bound
at the original point and the literal A(ii) degree/freedom window. -/
theorem coray_case_Aii_integral_originalClosedPoint_regular_or_three_dvd_normalizationConstantsRank
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 2 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ≤
      3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 -
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 < 3) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    IsRegularLocalRing (X.presheaf.stalk P.1) ∨
      3 ∣ Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ toBase I)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let a := Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
    (SheafOfModules.unit N.ringCatSheaf) ⊤)
  change IsRegularLocalRing (X.presheaf.stalk P.1) ∨ 3 ∣ a
  by_cases hregular : IsRegularLocalRing (X.presheaf.stalk P.1)
  · exact Or.inl hregular
  · apply Or.inr
    by_contra hthree
    have hn : 0 < n := by omega
    have hdiv : a ∣ 3 * n := projectiveIntersection_genericNormalization_constantsRank_dvd_three_mul
      p q hp hp0 n hq hnot
    have hdivn : a ∣ n := degree_delta_dvd_l_of_dvd_three_l a n hthree hdiv
    have han : a ≤ n := Nat.le_of_dvd hn hdivn
    have hlargeOr := projectiveIntersection_integral_originalClosedPoint_regular_or_fullConstants_degree_bound
      p q hp hp0 n hn hq hnot P
    have hlargeBound := hlargeOr.resolve_left hregular
    have hlargeChoose : pi.residueDegree P.1 + 1 ≤ a + (3 * n.choose 2 + 1) := by
      rw [coray_choose_genus_eq_euler_bound n]
      exact hlargeBound
    exact aii_smallConstants_contradiction n a (pi.residueDegree P.1)
      hlarge han hlargeChoose hdegree hfreedom

end PfaffianDescent.Coray

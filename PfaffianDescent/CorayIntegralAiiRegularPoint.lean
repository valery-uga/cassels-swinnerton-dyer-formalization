import PfaffianDescent.NormalizationResidueGlobalTransport
import PfaffianDescent.CorayNormalizationConstantsHyperplaneCycle
import PfaffianDescent.CorayIntegralFullConstantsNormalizationDefectBound

/-! Source only. Genuine integral A(ii) regularity of the original point.
This does not assert geometric integrality or a complete Coray descent. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The A(ii) degree window is incompatible with twice-point-degree defect
when full constants have rank at most 3*n and the genuine Euler defect bound
holds. All quantities here are ordinary natural numbers. -/
theorem aii_twiceDegree_fullConstants_contradiction
    (n a d delta : ℕ) (hn : 2 ≤ n) (ha : a ≤ 3 * n)
    (hupper : delta + 1 ≤ a + (3 * n.choose 2 + 1))
    (hlower : 2 * d ≤ delta)
    (hdegree : d ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 - d < 3) : False := by
  have hstep : 3 * (n + 1).choose 2 = 3 * n.choose 2 + 3 * n := by
    rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    norm_num only at *
    omega
  have hchoose : 3 ≤ (n + 1).choose 2 := by
    have hmono := Nat.choose_le_choose 2 (show 3 ≤ n + 1 by omega)
    simpa only [show Nat.choose 3 2 = 3 by decide] using hmono
  omega

/-- An actual point of degree prime to three in the literal A(ii) degree
window on the actual INTEGRAL whole cubic/degree-n intersection is regular.
The constants-divisibility alternative is eliminated by the actual original-K
global defect lower bound and the proved full-constants Euler upper bound.
No geometric-integrality, regularity, lift, defect or desired-outcome premise. -/
theorem coray_case_Aii_integral_originalClosedPoint_isRegularLocalRing
    {K : Type u} [Field K] [CharZero K]
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
    IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  let Q := genericNormalizationQuotientSheaf X
  let a := Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
    (SheafOfModules.unit N.ringCatSheaf) ⊤)
  let delta := Module.finrank K (SchemeModuleGlobalSectionsOver pi Q)
  have hn : 0 < n := by omega
  have hregularOr := coray_case_Aii_integral_originalClosedPoint_regular_or_three_dvd_normalizationConstantsRank
    p q hp hp0 n hlarge hq hnot P hdegree hfreedom
  change IsRegularLocalRing (X.presheaf.stalk P.1) ∨ 3 ∣ a at hregularOr
  rcases hregularOr with hregular | hthree
  · exact hregular
  · exfalso
    have hdiv : a ∣ 3 * n := projectiveIntersection_genericNormalization_constantsRank_dvd_three_mul
      p q hp hp0 n hq hnot
    have ha : a ≤ 3 * n := Nat.le_of_dvd (by omega) hdiv
    have hlower : 2 * pi.residueDegree P.1 ≤ delta :=
      projectiveIntersection_three_constants_globalDefect_ge_twice_point_degree
        p q hp hp0 n hq hnot P hcop hthree
    have hupperEuler : delta + 1 ≤ a + (1 + 3 * n * (n - 1) / 2) := by
      have hbound :
          Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) +
              Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) + 1 ≤
            a + (1 + 3 * n * (n - 1) / 2) :=
        projectiveIntersection_integral_genericNormalization_cohomology_one_add_globalQuotient_fullConstants_bound
          p q hp hp0 n hn hq hnot
      have hQ : delta = Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) :=
        (schemeModuleGlobalSectionsLinearEquivOpenTop pi Q).finrank_eq
      omega
    have hupper : delta + 1 ≤ a + (3 * n.choose 2 + 1) := by
      rw [coray_choose_genus_eq_euler_bound n]
      exact hupperEuler
    exact aii_twiceDegree_fullConstants_contradiction n a (pi.residueDegree P.1) delta
      hlarge ha hupper hlower hdegree hfreedom

end PfaffianDescent.Coray

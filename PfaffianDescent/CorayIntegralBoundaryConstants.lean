import PfaffianDescent.NormalizationLiftedResidueGeneralBound
import PfaffianDescent.CorayNormalizationConstantsHyperplaneCycle
import PfaffianDescent.CorayProjectiveNormalizationAdditiveSingularityDegree
import Mathlib.Data.Nat.GCD.Basic

/-! Source-only original full-constants control at the integral boundary.
The lifted residue/global defect relation is constructed by the new generic
geometry leaf. No geometric integrality or replacement curve is used. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact natural-number identity for the boundary degree. -/
theorem coray_boundaryDegree_twice_eq (n d : ℕ)
    (hd : d = 3 * n.choose 2 + 1) : 2 * d = 3 * n * (n - 1) + 2 := by
  have htwo : 2 * n.choose 2 = n * (n - 1) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose n 2
    rw [show Nat.factorial 2 = 2 by decide] at h
    simpa only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      mul_one, mul_comm] using h.symm
  calc
    2 * d = 2 * (3 * n.choose 2 + 1) := congrArg (fun x : ℕ => 2 * x) hd
    _ = 3 * (2 * n.choose 2) + 2 := by ring
    _ = 3 * n * (n - 1) + 2 := by rw [htwo]; ring

/-- At boundary degree d, full constants a>=3 dividing 3n and the same
actual lifted degree E force E>=3d. Only genuine degree divisibilities enter.
The exceptional gcd2,a4 possibility is excluded by the boundary identity. -/
theorem coray_boundaryConstants_liftedDegree_ge_three_mul
    (n a d E : ℕ) (hd : d = 3 * n.choose 2 + 1) (ha : 3 ≤ a)
    (haThreeN : a ∣ 3 * n) (haE : a ∣ E) (hdE : d ∣ E) (hEpos : 0 < E) :
    3 * d ≤ E := by
  let g := Nat.gcd a d
  have hgA : g ∣ a := Nat.gcd_dvd_left a d
  have hgD : g ∣ d := Nat.gcd_dvd_right a d
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left d (by omega)
  have hgThreeN : g ∣ 3 * n := dvd_trans hgA haThreeN
  have hgprod : g ∣ 3 * n * (n - 1) := dvd_mul_of_dvd_left hgThreeN _
  have hgTwod : g ∣ 2 * d := dvd_mul_of_dvd_right hgD 2
  have htwod := coray_boundaryDegree_twice_eq n d hd
  have hgSum : g ∣ 3 * n * (n - 1) + 2 := htwod ▸ hgTwod
  have hgTwo : g ∣ 2 := (Nat.dvd_add_iff_right hgprod).mpr hgSum
  have hgle : g ≤ 2 := Nat.le_of_dvd (by decide) hgTwo
  have hcases : g = 1 ∨ g = 2 := by omega
  have hlcmle : Nat.lcm a d ≤ E := Nat.le_of_dvd hEpos (Nat.lcm_dvd haE hdE)
  have hproduct : g * Nat.lcm a d = a * d := Nat.gcd_mul_lcm a d
  rcases hcases with hgOne | hgTwoEq
  · rw [hgOne, one_mul] at hproduct
    exact (Nat.mul_le_mul_right d ha).trans (hproduct.symm.le.trans hlcmle)
  · have haEven : 2 ∣ a := hgTwoEq ▸ hgA
    have hdEven : 2 ∣ d := hgTwoEq ▸ hgD
    have hnotFour : a ≠ 4 := by
      intro haFour
      have hfourThreeN : 4 ∣ 3 * n := by simpa only [haFour] using haThreeN
      have hfourprod : 4 ∣ 3 * n * (n - 1) := dvd_mul_of_dvd_left hfourThreeN _
      have hfourTwod : 4 ∣ 2 * d := by
        obtain ⟨k, hk⟩ := hdEven
        refine ⟨k, ?_⟩
        rw [hk]
        ring
      have hfourSum : 4 ∣ 3 * n * (n - 1) + 2 := htwod ▸ hfourTwod
      have hfourTwo : 4 ∣ 2 := (Nat.dvd_add_iff_right hfourprod).mpr hfourSum
      exact (by decide : ¬ 4 ∣ 2) hfourTwo
    have haSix : 6 ≤ a := by
      obtain ⟨k, hk⟩ := haEven
      omega
    have hmul : 6 * d ≤ a * d := Nat.mul_le_mul_right d haSix
    rw [hgTwoEq] at hproduct
    have hlcmLower : 3 * d ≤ Nat.lcm a d := by omega
    exact hlcmLower.trans hlcmle

/-- Boundary n>=3 excludes full constants rank>=3 using actual lifted
residue/global-defect bounds. This arithmetic cut is independent of geometry. -/
theorem coray_boundaryConstants_largeRank_contradiction
    (n a d delta E : ℕ) (hn : 3 ≤ n) (hd : d = 3 * n.choose 2 + 1)
    (ha : 3 ≤ a) (haThreeN : a ∣ 3 * n) (haE : a ∣ E) (hdE : d ∣ E)
    (hEpos : 0 < E) (hEbound : E ≤ d + delta) (hupper : delta + 1 ≤ a + d) : False := by
  have hresidue := coray_boundaryConstants_liftedDegree_ge_three_mul n a d E hd ha haThreeN haE hdE hEpos
  have haUpper : a ≤ 3 * n := Nat.le_of_dvd (by omega) haThreeN
  have htwod := coray_boundaryDegree_twice_eq n d hd
  have hprod : 6 * n ≤ 3 * n * (n - 1) := by
    calc
      6 * n = 3 * n * 2 := by ring
      _ ≤ 3 * n * (n - 1) := Nat.mul_le_mul_left (3 * n) (by omega)
  omega

/-- The actual full-constants Euler bound, specialized only to the natural
boundary equation for the SAME original point. No normalization constants
rank-one assertion or geometric-integrality hypothesis is introduced. -/
theorem projectiveIntersection_integral_boundary_fullConstants_globalDefect_bound
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 =
      1 + 3 * n * (n - 1) / 2) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    Module.finrank K (SchemeModuleGlobalSectionsOver (toBase I)
      (genericNormalizationQuotientSheaf X)) + 1 ≤
      Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ toBase I)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) + (toBase I).residueDegree P.1 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  let Q := genericNormalizationQuotientSheaf X
  let a := Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
    (SheafOfModules.unit N.ringCatSheaf) ⊤)
  let delta := Module.finrank K (SchemeModuleGlobalSectionsOver pi Q)
  let d := pi.residueDegree P.1
  have hbound :
      Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) +
          Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) + 1 ≤
        a + (1 + 3 * n * (n - 1) / 2) :=
    projectiveIntersection_integral_genericNormalization_cohomology_one_add_globalQuotient_fullConstants_bound
      p q hp hp0 n hn hq hnot
  have hQ : delta = Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) :=
    (schemeModuleGlobalSectionsLinearEquivOpenTop pi Q).finrank_eq
  have hdeg : d = 1 + 3 * n * (n - 1) / 2 := hPdegree
  change delta + 1 ≤ a + d
  omega

/-- For the literal INTEGRAL whole intersection at boundary degree and
n>=3, the FULL normalization constants rank is at most TWO. The actual
lifted residue degree/global defect bridge and degree divisibility eliminate
larger constants ranks; no desired constants bound is a premise. -/
theorem projectiveIntersection_integral_boundary_normalizationConstantsRank_le_two
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 3 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 =
      1 + 3 * n * (n - 1) / 2) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ toBase I)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) ≤ 2 := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let a := Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
    (SheafOfModules.unit N.ringCatSheaf) ⊤)
  let delta := Module.finrank K (SchemeModuleGlobalSectionsOver pi (genericNormalizationQuotientSheaf X))
  let d := pi.residueDegree P.1
  change a ≤ 2
  by_contra hnotSmall
  have ha : 3 ≤ a := by omega
  have hadiv : a ∣ 3 * n := projectiveIntersection_genericNormalization_constantsRank_dvd_three_mul
    p q hp hp0 n hq hnot
  have hd : d = 3 * n.choose 2 + 1 := hPdegree.trans (coray_choose_genus_eq_euler_bound n).symm
  obtain ⟨Q, _hQP, haE, hdE, hEpos, hEbound⟩ :=
    projectiveIntersection_genericNormalization_exists_liftedResidueDegree_divisibilities_and_globalDefect_bound
      p q hp hp0 n hq hnot P
  let E := (ν ≫ pi).residueDegree Q.1
  have haENative : a ∣ E := haE
  have hdENative : d ∣ E := hdE
  have hEposNative : 0 < E := hEpos
  have hEboundNative : E ≤ d + delta := hEbound
  have hupper : delta + 1 ≤ a + d :=
    projectiveIntersection_integral_boundary_fullConstants_globalDefect_bound
      p q hp hp0 n (by omega) hq hnot P hPdegree
  exact coray_boundaryConstants_largeRank_contradiction n a d delta E hlarge hd ha hadiv
    haENative hdENative hEposNative hEboundNative hupper

/-- Integral boundary A(iii), n>=3: the SAME original point is regular
when the SAME curve carries its disjoint reduced singular degree-three
support. The actual a<=2 bound is derived internally; D3 gives the actual
additive singularity contradiction. No geometric integrality, regularity,
constants-rank bound or unrelated surface cycle is a premise. -/
theorem projectiveIntersection_integral_originalClosedPoint_isRegularLocalRing_at_boundary_of_singular_reducedDegreeThree
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 3 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 =
      1 + 3 * n * (n - 1) / 2)
    (z : EffectiveZeroCycle (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hred : ∀ Q ∈ z.support, z Q = 1)
    (hzdegree : EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) z = 3)
    (hdisjoint : P ∉ z.support)
    (hzsing : ∀ Q ∈ z.support, ¬ IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk Q.1)) :
    IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let a := Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
    (SheafOfModules.unit N.ringCatSheaf) ⊤)
  let delta := Module.finrank K (SchemeModuleGlobalSectionsOver pi (genericNormalizationQuotientSheaf X))
  let d := pi.residueDegree P.1
  have ha : a ≤ 2 := projectiveIntersection_integral_boundary_normalizationConstantsRank_le_two
    p q hp hp0 n hlarge hq hnot P hPdegree
  have hupper : delta + 1 ≤ a + d :=
    projectiveIntersection_integral_boundary_fullConstants_globalDefect_bound
      p q hp hp0 n (by omega) hq hnot P hPdegree
  by_contra hsing
  have hlower : d + 3 ≤ delta :=
    projectiveIntersection_genericNormalization_nonregular_point_add_reduced_degreeThree_le_globalDefect
      p q hp hp0 n hq hnot P z hred hzdegree hdisjoint hsing hzsing
  omega

end PfaffianDescent.Coray

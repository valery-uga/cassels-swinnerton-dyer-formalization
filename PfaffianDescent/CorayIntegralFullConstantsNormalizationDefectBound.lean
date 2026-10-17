import PfaffianDescent.CorayProjectiveOriginalPointStrictRegularity
import PfaffianDescent.CorayProjectiveNormalizationBaseEuler
import PfaffianDescent.CorayProjectiveIntersectionCohomologyOneBound

/-! Source-only new ordinary bounds: the actual full normalization constants
rank is retained. No GI, desired defect bound, regularity, section, finite-H1
or rank-one constants premise is supplied. This is not full Coray reduction. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary rank arithmetic retaining both full constants and full defect. -/
theorem normalizationFullConstants_euler_bound_nat
    (a b c delta G : ℕ)
    (heuler : (a : ℤ) - (b : ℤ) = 1 - (c : ℤ) + (delta : ℤ))
    (hc : c ≤ G) : b + delta + 1 ≤ a + G := by
  omega

/-- Whole integral p/q intersection: retain the full constants rank rather
than assuming GI to replace it by one. All original scalar actions remain. -/
theorem projectiveIntersection_integral_genericNormalization_cohomology_one_add_globalQuotient_fullConstants_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
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
    Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) +
        Module.finrank K (SchemeModuleOpenSectionsOver pi
          (genericNormalizationQuotientSheaf X) ⊤) + 1 ≤
      Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) + (1 + 3 * n * (n - 1) / 2) := by
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
  have hbase := projectiveIntersection_genericNormalization_unit_baseEuler_eq_curveH1_and_quotient
    p q hp hp0 n hn hq hnot
  have hcurve := projectiveIntersection_unit_cohomology_one_finrank_le_native
    p q hp hp0 n hn hq hnot
  have hQ := (schemeModuleGlobalSectionsLinearEquivOpenTop pi Q).finrank_eq
  dsimp only [I, X, pi, N, ν, Q] at hbase hcurve hQ ⊢
  have h := normalizationFullConstants_euler_bound_nat _ _ _ _ _ hbase hcurve
  omega

/-- Without GI, either the actual original point is regular, or its full
original degree plus one is bounded by G_n plus the actual normalization
constants rank. The latter is a real remaining alternative, not discarded. -/
theorem projectiveIntersection_integral_originalClosedPoint_regular_or_fullConstants_degree_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq))) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    IsRegularLocalRing (X.presheaf.stalk P.1) ∨
      pi.residueDegree P.1 + 1 ≤
        Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
          (SheafOfModules.unit N.ringCatSheaf) ⊤) + (1 + 3 * n * (n - 1) / 2) := by
  classical
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
  by_cases hregular : IsRegularLocalRing (X.presheaf.stalk P.1)
  · exact Or.inl hregular
  · apply Or.inr
    have hpoint := projectiveIntersection_genericNormalization_nonregular_originalClosedPoint_degree_le_globalDefect
      p q hp hp0 n hq hnot P hregular
    have hbound := projectiveIntersection_integral_genericNormalization_cohomology_one_add_globalQuotient_fullConstants_bound
      p q hp hp0 n hn hq hnot
    have hQ := (schemeModuleGlobalSectionsLinearEquivOpenTop pi Q).finrank_eq
    dsimp only [I, X, pi, N, ν, Q] at hpoint hbound hQ ⊢
    omega

end PfaffianDescent.Coray

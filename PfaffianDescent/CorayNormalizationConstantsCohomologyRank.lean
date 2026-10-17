import PfaffianDescent.SchemeModuleGlobalConstantsExtScalarTower
import PfaffianDescent.CorayOwnComponentProperConstants
import PfaffianDescent.CorayProjectiveNormalizationIntrinsicH1FiniteCore
import PfaffianDescent.CorayIntegralFullConstantsNormalizationDefectBound
import Mathlib.LinearAlgebra.Dimension.Free

/-! Source-only genuine normalization constants/H1 rank reduction. The actual
canonical global-constants scalar tower preserves the independently induced
original K action. Normalization H1 finiteness is derived internally from
primitive original p/q data. No GI, desired divisibility, regularity or H1
vanishing is supplied as an endpoint premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Arbitrary proper integral X: its genuine global field acts on installed
scheme cohomology. The resulting tower derives its full H0 rank divisibility
without an assumed scalar comparison, finite-H1 or rank relation. -/
theorem integralProper_globalUnitSections_finrank_dvd_cohomology_finrank
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    [HasExt.{u} X.Modules] (pi : X ⟶ Spec (.of K)) [IsProper pi]
    (M : X.Modules) (n : ℕ) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.finrank K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) ∣
      Module.finrank K (schemeModuleCohomology X M n) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  have hA : IsField Γ(X, ⊤) := isField_of_universallyClosed K pi
  letI : Field Γ(X, ⊤) := hA.toField
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  letI : Linear Γ(X, ⊤) X.Modules := schemeModulesLinearOver X.toSpecΓ
  letI : IsScalarTower K Γ(X, ⊤) (schemeModuleCohomology X M n) :=
    schemeModuleExtGlobalConstantsScalarTower pi hA
      (SheafOfModules.unit X.ringCatSheaf) M n
  have hdiv : Module.finrank K Γ(X, ⊤) ∣
      Module.finrank K (schemeModuleCohomology X M n) :=
    Module.finrank_dvd_finrank_right K Γ(X, ⊤) (schemeModuleCohomology X M n)
  have hunit := (schemeModuleUnitTopOriginalRingLinearEquiv pi).finrank_eq
  exact hunit.symm ▸ hdiv


/-- The original integral p/q curve's ACTUAL canonical normalization retains
its original K scalar action. Its FULL constants rank divides its intrinsic
H1 rank; properness and normalization finiteness are constructed internally. -/
theorem projectiveIntersection_genericNormalization_constantsRank_dvd_cohomologyOneRank
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
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ toBase I)
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ toBase I)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) ∣
      Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsIntegral N := inferInstance
  letI : IsFinite ν := integralScheme_genericNormalization_isFinite X (toBase I)
  letI : IsProper (ν ≫ toBase I) := inferInstance
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ toBase I)
  exact integralProper_globalUnitSections_finrank_dvd_cohomology_finrank
    N (ν ≫ toBase I) (SheafOfModules.unit N.ringCatSheaf) 1


private theorem constantsRank_absorbed_defect_contradiction
    (a b delta G d : ℕ) (hab : a ≤ b)
    (hbound : b + delta + 1 ≤ a + G) (hpoint : d ≤ delta) (hdegree : G ≤ d) : False := by
  omega

/-- A(ii)'s regularity bottleneck without GI: for an original point of degree
at least G_n, either its native curve stalk is regular OR the SAME canonical
normalization's intrinsic H1 actually vanishes. The constants correction is
absorbed when H1 is nonzero; the remaining genus-zero case is not discarded. -/
theorem projectiveIntersection_integral_originalClosedPoint_regular_or_normalizationH1_subsingleton
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hdegree : 1 + 3 * n * (n - 1) / 2 ≤
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    IsRegularLocalRing (X.presheaf.stalk P.1) ∨
      Subsingleton (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) := by
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
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  change IsRegularLocalRing (X.presheaf.stalk P.1) ∨ Subsingleton (schemeModuleCohomology N O 1)
  by_cases hregular : IsRegularLocalRing (X.presheaf.stalk P.1)
  · exact Or.inl hregular
  · apply Or.inr
    letI : Module.Finite K (schemeModuleCohomology N O 1) :=
      projectiveIntersection_genericNormalization_unit_cohomology_one_finite_native p q hp hp0 n hq hnot
    apply (Module.finrank_zero_iff (R := K) (M := schemeModuleCohomology N O 1)).mp
    by_contra hb
    have hpos : 0 < Module.finrank K (schemeModuleCohomology N O 1) := Nat.pos_of_ne_zero hb
    have hdiv := projectiveIntersection_genericNormalization_constantsRank_dvd_cohomologyOneRank
      p q hp hp0 n hq hnot
    have hab := Nat.le_of_dvd hpos hdiv
    have hpoint := projectiveIntersection_genericNormalization_nonregular_originalClosedPoint_degree_le_globalDefect
      p q hp hp0 n hq hnot P hregular
    have hbound := projectiveIntersection_integral_genericNormalization_cohomology_one_add_globalQuotient_fullConstants_bound
      p q hp hp0 n hn hq hnot
    have hQ := (schemeModuleGlobalSectionsLinearEquivOpenTop pi Q).finrank_eq
    have hpointOpen : pi.residueDegree P.1 ≤
        Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) := hpoint.trans_eq hQ
    exact constantsRank_absorbed_defect_contradiction _ _ _ _ _ hab hbound hpointOpen hdegree

end PfaffianDescent.Coray

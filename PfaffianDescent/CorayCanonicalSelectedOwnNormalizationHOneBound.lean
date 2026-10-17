import PfaffianDescent.CorayCanonicalSelectedOwnNativeEulerGenusBound
import PfaffianDescent.CorayPerfectOwnNormalizationEuler

/-! SOURCE ONLY. Original selected-component normalization Euler bound.
The actual full constants ranks on C and N and the full actual quotient
remain in the pre-existing canonical Euler comparison. -/
noncomputable section
namespace PfaffianDescent.Coray
open CategoryTheory.Abelian
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine original component input plus its explicit degree=3r branch
implies the OWN normalization Euler lower bound. CharZero supplies the
perfect-field prerequisite of the genuine existing normalization comparison.
No genus, Euler, constants-field or normalization-rank premise is supplied. -/
theorem selectedProjectiveMinimalComponent_normalization_hOne_twice_upper_bound_with_full_constants001
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) (r : ℕ) (hdegree : actualCurveCoordinateHilbertDegree C = 3 * r) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hCmin.isPrime P
    let X := scheme C
    let pi := toBase C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    letI : AddCommGroup (schemeModuleCohomology X OX 1) := Ext.instAddCommGroup
    letI : AddCommGroup (schemeModuleCohomology N ON 1) := Ext.instAddCommGroup
    letI : Module K (schemeModuleCohomology X OX 1) := Ext.instModule
    letI : Module K (schemeModuleCohomology N ON 1) := Ext.instModule
    let Q : X.Modules := genericNormalizationQuotientSheaf X
    2 * (Module.finrank K (schemeModuleCohomology N ON 1) : ℤ) ≤
      2 * (Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi) ON ⊤) : ℤ) +
        (3 * r * (r - 1) : ℕ) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hCmin.isPrime P
  let X := scheme C
  let pi := toBase C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  letI : AddCommGroup (schemeModuleCohomology X OX 1) := Ext.instAddCommGroup
  letI : AddCommGroup (schemeModuleCohomology N ON 1) := Ext.instAddCommGroup
  letI : Module K (schemeModuleCohomology X OX 1) := Ext.instModule
  letI : Module K (schemeModuleCohomology N ON 1) := Ext.instModule
  let Q : X.Modules := genericNormalizationQuotientSheaf X
  have hC := selectedProjectiveMinimalComponent_ownUnitNativeEuler_twice_lower_bound001
    p q hp hp0 n hq hnot C hCmin P r hdegree
  have hN := perfectField_selectedProjectivePrimeComponent_genericNormalization_unit_baseEuler_eq_curveEuler_add_fullQuotient
    p q hp hp0 n hq hnot C hCmin.le hCmin.isPrime P
  change (Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi) ON ⊤) : ℤ) -
      (Module.finrank K (schemeModuleCohomology N ON 1) : ℤ) =
    ownUnitNativeEuler C + (Module.finrank K (SchemeModuleGlobalSectionsOver pi Q) : ℤ) at hN
  have hQ : (0 : ℤ) ≤ (Module.finrank K (SchemeModuleGlobalSectionsOver pi Q) : ℤ) := by
    exact_mod_cast Nat.zero_le (Module.finrank K (SchemeModuleGlobalSectionsOver pi Q))
  have hNLower : 0 ≤
      2 * ((Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi) ON ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N ON 1) : ℤ)) +
          (3 * r * (r - 1) : ℕ) := by
    rw [hN]
    linarith
  linarith

end PfaffianDescent.Coray

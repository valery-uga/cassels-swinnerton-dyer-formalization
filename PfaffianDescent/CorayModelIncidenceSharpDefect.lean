import PfaffianDescent.CorayModelIncidenceOwnGenusWindow
import PfaffianDescent.CorayCanonicalSelectedOwnNativeEulerGenusBound
import PfaffianDescent.CorayComponentAiiRegularity
import PfaffianDescent.CorayGeometricallyIntegralNormalizationConstants
import PfaffianDescent.CorayPerfectOwnNormalizationConstantsTower

/-! Actual sharp normalization defect on SAME GI model, with constants rank derived. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {F : Type u} [Field F] [CharZero F]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Ordinary integer cut for the SAME normalization Euler comparison. Keeping
all ranks abstract prevents arithmetic preprocessing from expanding native
module/normalization aliases into different atoms. -/
private theorem modelSharpDefect_integerEuler_bound001
    (chi hOne defect genus error : ℤ)
    (hEuler : 1 - hOne = chi + defect)
    (hSharp : 0 ≤ 2 * chi + error) (hNonnegative : 0 ≤ hOne)
    (hTwice : 2 * genus = 2 + error) : defect ≤ genus := by
  linarith only [hEuler, hSharp, hNonnegative, hTwice]


/-- The model's actual geometric integrality derives normalization constants
rank1. Its genuine sharp Euler bound and actual full quotient comparison then
derive the OWN-degree defect bound, without a supplied rank/genus/defect input. -/
theorem selectedMinimalComponent_geometricallyIntegral_genericNormalization_sharpDefect_bound001
    (p q : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) F)))
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hD : D.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    [GeometricallyIntegral (toBase D)]
    (P : closedPoints (scheme D)) (lambda : ℕ)
    (hMu : actualCurveCoordinateHilbertDegree D = 3 * lambda) :
    letI : IsIntegral (scheme D) := homogeneousPrime_projectiveScheme_isIntegral D hD.isPrime P.1
    Module.finrank F (SchemeModuleGlobalSectionsOver (toBase D)
      (genericNormalizationQuotientSheaf (scheme D))) ≤ 1 + 3 * lambda.choose 2 := by
  letI : IsIntegral (scheme D) := homogeneousPrime_projectiveScheme_isIntegral D hD.isPrime P.1
  let X := scheme D
  let pi := toBase D
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  let delta := Module.finrank F (SchemeModuleGlobalSectionsOver pi (genericNormalizationQuotientSheaf X))
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  letI : Linear F N.Modules := schemeModulesLinearOver (nu ≫ pi)
  have hFinite : Module.Finite F (SchemeModuleOpenSectionsOver (nu ≫ pi) ON ⊤) :=
    (perfectField_homogeneousPrime_genericNormalization_originalConstants_finite_and_finrank_dvd
      D hD.isPrime P.1).2.2.1
  have hConstants : Module.finrank F (SchemeModuleOpenSectionsOver (nu ≫ pi) ON ⊤) = 1 :=
    integralGenericNormalization_unit_topSections_finrank_eq_one_of_geometricallyIntegral X pi hFinite
  have hSharp : 0 ≤ 2 * ownUnitNativeEuler D + (3 * lambda * (lambda - 1) : ℕ) :=
    selectedProjectiveMinimalComponent_ownUnitNativeEuler_twice_lower_bound001
      p q hp hp0 n hq hnot D hD P.1 lambda hMu
  have hEuler :=
    perfectField_selectedProjectivePrimeComponent_genericNormalization_unit_baseEuler_eq_curveEuler_add_fullQuotient
      p q hp hp0 n hq hnot D hD.le hD.isPrime P.1
  change (Module.finrank F (SchemeModuleOpenSectionsOver (nu ≫ pi) ON ⊤) : ℤ) -
      (Module.finrank F (schemeModuleCohomology N ON 1) : ℤ) =
        ownUnitNativeEuler D + (delta : ℤ) at hEuler
  rw [hConstants] at hEuler
  have hNonnegative : (0 : ℤ) ≤ (Module.finrank F (schemeModuleCohomology N ON 1) : ℤ) := by
    exact_mod_cast Nat.zero_le (Module.finrank F (schemeModuleCohomology N ON 1))
  have hTwice : (2 : ℤ) * ((1 + 3 * lambda.choose 2 : ℕ) : ℤ) =
      2 + ((3 * lambda * (lambda - 1) : ℕ) : ℤ) := by
    exact_mod_cast coray_twice_chooseGenus_polynomial001 lambda
  have hEulerNative : (1 : ℤ) -
      (Module.finrank F (schemeModuleCohomology N ON 1) : ℤ) =
        ownUnitNativeEuler D + (delta : ℤ) := by
    simpa only [Nat.cast_one] using hEuler
  have hDefect : (delta : ℤ) ≤ ((1 + 3 * lambda.choose 2 : ℕ) : ℤ) :=
    modelSharpDefect_integerEuler_bound001
      (ownUnitNativeEuler D)
      (Module.finrank F (schemeModuleCohomology N ON 1) : ℤ)
      (delta : ℤ) ((1 + 3 * lambda.choose 2 : ℕ) : ℤ)
      ((3 * lambda * (lambda - 1) : ℕ) : ℤ)
      hEulerNative hSharp hNonnegative hTwice
  change delta ≤ 1 + 3 * lambda.choose 2
  exact_mod_cast hDefect

end PfaffianDescent.Coray

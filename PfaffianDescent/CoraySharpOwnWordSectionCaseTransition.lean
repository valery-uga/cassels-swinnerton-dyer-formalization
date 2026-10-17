import PfaffianDescent.CorayOwnComponentWordSection
import PfaffianDescent.CorayCanonicalSelectedOwnNativeEulerGenusBound
import PfaffianDescent.CorayModelIncidenceOwnGenusWindow

/-! Sharp actual word-section producer from SAME native Euler, retaining full constants. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Genuine sharp OWN-degree nonzero section, with the full actual quotient
and both constant ranks retained. No chosen nonzero section, genus, H1,
rank-one constants, geometric integrality or desired point outcome is input. -/
theorem selectedMinimalComponent_genericNormalization_signedWord_exists_nonzero_section_of_sharp_weight_add_defect001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) (lambda : ℕ)
    (hMu : actualCurveCoordinateHilbertDegree C = 3 * lambda) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ((1 + 3 * lambda.choose 2 : ℕ) : ℤ) ≤
        schemeModuleSignedClosedPointTensorWeightSum pi ops +
          (Module.finrank K (SchemeModuleGlobalSectionsOver (toBase C)
            (genericNormalizationQuotientSheaf X)) : ℤ) →
        ∃ s : SchemeModuleOpenSectionsOver pi W ⊤, s ≠ 0 := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  let piX := toBase C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ piX
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  let Q := genericNormalizationQuotientSheaf X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver piX
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  have hSharp : 0 ≤ 2 * ownUnitNativeEuler C + (3 * lambda * (lambda - 1) : ℕ) :=
    selectedProjectiveMinimalComponent_ownUnitNativeEuler_twice_lower_bound001
      p q hp hp0 n hq hnot C hmin P lambda hMu
  have hEuler :=
    perfectField_selectedProjectivePrimeComponent_genericNormalization_unit_baseEuler_eq_curveEuler_add_fullQuotient
      p q hp hp0 n hq hnot C hmin.le hmin.isPrime P
  change (Module.finrank K (SchemeModuleOpenSectionsOver pi ON ⊤) : ℤ) -
      (Module.finrank K (schemeModuleCohomology N ON 1) : ℤ) =
        ownUnitNativeEuler C + (Module.finrank K (SchemeModuleGlobalSectionsOver piX Q) : ℤ) at hEuler
  have hTwice : (2 : ℤ) * ((1 + 3 * lambda.choose 2 : ℕ) : ℤ) =
      2 + ((3 * lambda * (lambda - 1) : ℕ) : ℤ) := by
    exact_mod_cast coray_twice_chooseGenus_polynomial001 lambda
  dsimp only
  intro ops hw
  let W := schemeModuleIteratedSignedClosedPointTensor ON ops
  obtain ⟨_hRank, _hFinite0, _hFinite1, hChange⟩ :=
    selectedMinimalComponent_genericNormalization_signedWord_finite_and_euler_change
      p q hp hp0 n hq hnot C hmin P ops
  have hChangeNative :
      (Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N W 1) : ℤ) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi ON ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N ON 1) : ℤ) +
        schemeModuleSignedClosedPointTensorWeightSum pi ops := hChange
  have hwNative : ((1 + 3 * lambda.choose 2 : ℕ) : ℤ) ≤
      schemeModuleSignedClosedPointTensorWeightSum pi ops +
        (Module.finrank K (SchemeModuleGlobalSectionsOver piX Q) : ℤ) := hw
  have hNonnegative : (0 : ℤ) ≤ (Module.finrank K (schemeModuleCohomology N W 1) : ℤ) := by
    exact_mod_cast Nat.zero_le (Module.finrank K (schemeModuleCohomology N W 1))
  have hPositiveInt : (0 : ℤ) < (Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) : ℤ) := by
    linarith
  have hPositive : 0 < Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) := by
    exact_mod_cast hPositiveInt
  letI := Module.nontrivial_of_finrank_pos hPositive
  exact exists_ne 0

end PfaffianDescent.Coray

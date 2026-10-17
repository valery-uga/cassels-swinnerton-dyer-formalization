import PfaffianDescent.CorayClosedComponentIntrinsicH1Bound
import PfaffianDescent.CorayPerfectOwnNormalizationEuler
import PfaffianDescent.CorayPerfectOwnNormalizationIntrinsicH1Finite
import PfaffianDescent.CorayPerfectOwnNormalizationPointIdealRankOne
import PfaffianDescent.CorayPerfectOwnNormalizationConstantsTower
import PfaffianDescent.SchemeModuleFiniteSignedPointTensorIteration

/-! Source-only: arbitrary OWN normalization signed words have actual finite
Euler and a nonzero section in the constructed coarse genus window. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem integralProper_actualUnitSections_finrank_pos
    {X : Scheme.{u}} [IsIntegral X] (pi : X ⟶ Spec (.of K)) [IsProper pi] :
    0 < Module.finrank K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) := by
  obtain ⟨hfield, hfinite⟩ := integralProper_originalGlobalFunctions_field_and_unitSectionsFinite pi
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) := hfinite
  letI : Field Γ(X, ⊤) := hfield.toField
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  let E := schemeModuleUnitTopOriginalRingLinearEquiv pi
  letI : Nontrivial (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) := E.toEquiv.nontrivial_congr.mpr inferInstance
  exact Module.finrank_pos

/-- Actual arbitrary signed words on the SAME component normalization have
rank-one charts, finite original-K H0/H1 and exact weighted Euler change.
No nonzero section or base/final finiteness is a construction hypothesis. -/
theorem selectedMinimalComponent_genericNormalization_signedWord_finite_and_euler_change
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor O ops
      schemeModuleLocallyRankOne W ∧
        Module.Finite K (SchemeModuleOpenSectionsOver pi W ⊤) ∧
        Module.Finite K (schemeModuleCohomology N W 1) ∧
        (Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) : ℤ) -
            (Module.finrank K (schemeModuleCohomology N W 1) : ℤ) =
          (Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) : ℤ) -
            (Module.finrank K (schemeModuleCohomology N O 1) : ℤ) +
            schemeModuleSignedClosedPointTensorWeightSum pi ops := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase C
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase C)
  letI : LocallyOfFiniteType pi := inferInstance
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  have hO : schemeModuleLocallyRankOne O := fun x => ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  have h0 : Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) :=
    (perfectField_homogeneousPrime_genericNormalization_originalConstants_finite_and_finrank_dvd
      C hmin.isPrime P).2.2.1
  have h1 : Module.Finite K (schemeModuleCohomology N O 1) :=
    perfectField_selectedProjectivePrimeComponent_genericNormalization_unit_cohomology_one_finite_native
      p q hp hp0 n hq hnot C hmin.le hmin.isPrime P
  dsimp only
  intro ops
  have hM : ∀ Q : closedPoints N,
      let i := N.fromSpecResidueField Q.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
      schemeModuleLocallyRankOne (closedImmersionModule i) :=
    fun Q => perfectField_selectedProjectiveMinimalComponent_genericNormalization_closedPoint_ideal_locallyRankOne
      p q hp hp0 n hq hnot C hmin P Q
  exact schemeModuleIteratedSignedClosedPointTensor_finite_and_h0_h1_change pi ops O hM hO h0 h1

/-- A nonzero OWN signed-word section is PRODUCED from the genuine Euler
window. Both full constants ranks remain, and actual quotient defect is kept.
No GI, regular original point, chosen cycle or nonzero section is assumed. -/
theorem selectedMinimalComponent_genericNormalization_signedWord_exists_nonzero_section_of_weight_add_defect_ge_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
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
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  let Q := genericNormalizationQuotientSheaf X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver piX
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  have hEuler :
      (Module.finrank K (SchemeModuleOpenSectionsOver pi ON ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N ON 1) : ℤ) =
      (Module.finrank K (SchemeModuleOpenSectionsOver piX OX ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology X OX 1) : ℤ) +
        (Module.finrank K (SchemeModuleGlobalSectionsOver piX Q) : ℤ) :=
    perfectField_selectedProjectivePrimeComponent_genericNormalization_unit_baseEuler_eq_curveEuler_add_fullQuotient
      p q hp hp0 n hq hnot C hmin.le hmin.isPrime P
  have hH1 : Module.finrank K (schemeModuleCohomology X OX 1) ≤ 1 + 3 * n * (n - 1) / 2 :=
    (projectiveIntersection_closedComponent_unit_cohomology_one_finite_finrank_le
      p q hp hp0 n hn hq hnot C hmin.le).2
  have hH0 : 0 < Module.finrank K (SchemeModuleOpenSectionsOver piX OX ⊤) :=
    integralProper_actualUnitSections_finrank_pos piX
  dsimp only
  intro ops hw
  let W := schemeModuleIteratedSignedClosedPointTensor ON ops
  obtain ⟨_hRank, _h0, _h1, hChange⟩ :=
    selectedMinimalComponent_genericNormalization_signedWord_finite_and_euler_change
      p q hp hp0 n hq hnot C hmin P ops
  have hChangeNative :
      (Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N W 1) : ℤ) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi ON ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N ON 1) : ℤ) +
        schemeModuleSignedClosedPointTensorWeightSum pi ops := hChange
  have hwNative : ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
      schemeModuleSignedClosedPointTensorWeightSum pi ops +
        (Module.finrank K (SchemeModuleGlobalSectionsOver piX Q) : ℤ) := hw
  have hpos : 0 < Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) := by omega
  letI := Module.nontrivial_of_finrank_pos hpos
  exact exists_ne 0

end PfaffianDescent.Coray

import PfaffianDescent.CorayOwnComponentProperConstants
import PfaffianDescent.CorayFiniteSchemeGenericNormalization

/-! SOURCE ONLY / UNVERIFIED. The SAME canonical generic normalization is
finite by the existing characteristic-zero normalization theorem, hence
proper over ORIGINAL K. Its OWN unit H0 is a finite field, and the literal
normalization pullback constructs the original-K constants-field tower.
No normalization finite/H0/rank certificate or residue-degree claim. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal normalization pullback, with both independently original-pi
K-actions retained. This map itself needs no finiteness, properness, GI,
characteristic-zero or constants-field premise. -/
def integralGenericNormalization_originalGlobalFunctionsPullbackAlgHom
    (X : Scheme.{u}) [IsIntegral X] (pi : X ⟶ Spec (.of K)) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
    letI : Algebra K Γ(N, ⊤) := (schemeOpenBaseRingHom (ν ≫ pi) ⊤).toAlgebra
    Γ(X, ⊤) →ₐ[K] Γ(N, ⊤) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  letI : Algebra K Γ(N, ⊤) := (schemeOpenBaseRingHom (ν ≫ pi) ⊤).toAlgebra
  refine { toRingHom := ν.appTop.hom, commutes' := ?_ }
  intro c
  change ν.appTop (schemeOpenBaseRingHom pi ⊤ c) =
    schemeOpenBaseRingHom (ν ≫ pi) ⊤ c
  rw [schemeOpenBaseRingHom_top_apply, schemeOpenBaseRingHom_top_apply]
  exact (congrArg (fun f : K →+* Γ(N, ⊤) => f c)
    (affineFunctionHom_comp ν pi)).symm

/-- Even before finite normalization is known, both OWN constants rings
are fields and literal normalization pullback is injective. Integrality
of the native normalization map supplies universal closedness; no locally
finite-type claim about its source is used in this Field-only leaf. -/
theorem integralProper_genericNormalization_originalConstants_field_and_pullback_injective
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
    letI : Algebra K Γ(N, ⊤) := (schemeOpenBaseRingHom (ν ≫ pi) ⊤).toAlgebra
    IsField Γ(X, ⊤) ∧ IsField Γ(N, ⊤) ∧
      Function.Injective
        (integralGenericNormalization_originalGlobalFunctionsPullbackAlgHom X pi) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsIntegral N := inferInstance
  letI : UniversallyClosed (ν ≫ pi) := inferInstance
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  letI : Algebra K Γ(N, ⊤) := (schemeOpenBaseRingHom (ν ≫ pi) ⊤).toAlgebra
  have hXfield : IsField Γ(X, ⊤) := isField_of_universallyClosed K pi
  have hNfield : IsField Γ(N, ⊤) := isField_of_universallyClosed K (ν ≫ pi)
  refine ⟨hXfield, hNfield, ?_⟩
  letI : Field Γ(X, ⊤) := hXfield.toField
  letI : Field Γ(N, ⊤) := hNfield.toField
  exact (integralGenericNormalization_originalGlobalFunctionsPullbackAlgHom X pi).injective

/-- Actual finite normalization, actual composite properness and original
global pullback derive finite OWN normalization constants and r_C | r_N.
The explicit CharZero boundary is that of the existing finite-normalization
producer. Neither constants field is assumed to equal K. -/
theorem integralProper_genericNormalization_originalConstants_finite_and_finrank_dvd
    [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    IsField Γ(X, ⊤) ∧ IsField Γ(N, ⊤) ∧
      Module.Finite K (SchemeModuleOpenSectionsOver (ν ≫ pi)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi
        (SheafOfModules.unit X.ringCatSheaf) ⊤) ∣
      Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsIntegral N := inferInstance
  letI : IsFinite ν := integralScheme_genericNormalization_isFinite X pi
  letI : IsProper (ν ≫ pi) := inferInstance
  obtain ⟨hNfield, hNfinite⟩ :=
    integralProper_originalGlobalFunctions_field_and_unitSectionsFinite (ν ≫ pi)
  have hXfield : IsField Γ(X, ⊤) := isField_of_universallyClosed K pi
  refine ⟨hXfield, hNfield, hNfinite, ?_⟩
  let A := Γ(X, ⊤)
  let B := Γ(N, ⊤)
  letI : Algebra K A := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  letI : Algebra K B := (schemeOpenBaseRingHom (ν ≫ pi) ⊤).toAlgebra
  letI : Field A := hXfield.toField
  letI : Field B := hNfield.toField
  let i : A →ₐ[K] B :=
    integralGenericNormalization_originalGlobalFunctionsPullbackAlgHom X pi
  letI : Algebra A B := i.toRingHom.toAlgebra
  letI : IsScalarTower K A B :=
    IsScalarTower.of_algebraMap_eq (fun c => (i.commutes c).symm)
  have hdiv : Module.finrank K A ∣ Module.finrank K B :=
    Module.finrank_dvd_finrank_right K A B
  have hXrank : Module.finrank K (SchemeModuleOpenSectionsOver pi
      (SheafOfModules.unit X.ringCatSheaf) ⊤) = Module.finrank K A :=
    (schemeModuleUnitTopOriginalRingLinearEquiv pi).finrank_eq
  have hNrank : Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) = Module.finrank K B :=
    (schemeModuleUnitTopOriginalRingLinearEquiv (ν ≫ pi)).finrank_eq
  exact hXrank.symm ▸ (hNrank.symm ▸ hdiv)

/-- An actual homogeneous prime component with an actual point derives
native integrality and properness. The SAME existing canonical normalization
then has finite original-K H0 and OWN constants rank divisible by r_C.
This is an OWN component statement, without whole-CI cohomology or any
regularity/geometric-integrality input. -/
theorem homogeneousPrime_genericNormalization_originalConstants_finite_and_finrank_dvd
    [CharZero K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    let X := scheme C
    letI : IsIntegral X := homogeneousPrime_projectiveScheme_isIntegral C hprime P
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    IsField Γ(X, ⊤) ∧ IsField Γ(N, ⊤) ∧
      Module.Finite K (SchemeModuleOpenSectionsOver (ν ≫ toBase C)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
        (SheafOfModules.unit X.ringCatSheaf) ⊤) ∣
      Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ toBase C)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) := by
  let X := scheme C
  letI : IsIntegral X := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  letI : IsProper (toBase C) := isProper_toBase C
  exact integralProper_genericNormalization_originalConstants_finite_and_finrank_dvd X (toBase C)

end PfaffianDescent.Coray

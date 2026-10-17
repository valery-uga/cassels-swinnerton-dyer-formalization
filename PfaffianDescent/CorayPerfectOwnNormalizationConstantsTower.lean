import PfaffianDescent.CorayOwnNormalizationConstantsTower
import PfaffianDescent.CorayPerfectFiniteSchemeGenericNormalization

/-! SOURCE ONLY / UNVERIFIED. Original PerfectField K application to SAME
OWN normalization. Actual finite normalization derives properness; actual
own original-pi H0 constants and literal pullback derive r_C | r_N.
094+093 DEEP accepted via combined strict audit851 at source freeze.
No singular point residue-divisibility, GI/constants=K or genus claim. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- SAME actual OWN normalization has finite original-K unit H0, both
actual constants rings are fields, and literal pullback derives r_C|r_N
for original perfect K. No normalization finiteness or rank premise. -/
theorem perfectField_integralProper_genericNormalization_originalConstants_finite_and_finrank_dvd
    [PerfectField K] (X : Scheme.{u}) [IsIntegral X]
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
  letI : IsFinite ν := perfectField_integralScheme_genericNormalization_isFinite X pi
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
theorem perfectField_homogeneousPrime_genericNormalization_originalConstants_finite_and_finrank_dvd
    [PerfectField K]
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
  exact perfectField_integralProper_genericNormalization_originalConstants_finite_and_finrank_dvd X (toBase C)


end PfaffianDescent.Coray

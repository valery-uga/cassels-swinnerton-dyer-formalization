import PfaffianDescent.P3GeneralNegativeTwistTopResidue
import PfaffianDescent.P3CanonicalTraceScalar
import PfaffianDescent.P3HomogeneousGlobalSectionsLinear
import PfaffianDescent.SchemeModuleBaseLinearCategory
import PfaffianDescent.SheafModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! The SAME all-m residue injection is linear for the independently defined
actual ambientToBase action. Actual multiplication by C(c) is proved equal
to the actual base-scalar coefficient endomorphism, on every actual open.
This proves finite intrinsic H³ for all negative twists, including m<4.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns all compiler checks.
-/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentLocalization
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ORIGINAL base constant on any actual open has the actual constant
polynomial value in the SAME stalk localization. Empty opens are included. -/
theorem p3AmbientOpenBaseScalar_value (c : K) (U : (Proj PS).Opens) (x : U) :
    ((schemeOpenBaseRingHom (ambientToBase (R := K) (σ := Fin 4)) U c).1 x).val =
      algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) (MvPolynomial.C c) := by
  change ((affineFunctionHom (ambientToBase (R := K) (σ := Fin 4)) c).1
    ⟨x.1, trivial⟩).val = _
  rw [p3AmbientBaseScalar_value K c x.1]
  exact Localization.mk_one_eq_algebraMap _

/-- Genuine equality of the independently pi-defined scalar endomorphism
with the ORIGINAL homogeneous multiplication map on the actual twist. -/
theorem p3NegativeTwist_scalarEndomorphism_eq_mulHomogeneous (m : ℕ) (c : K) :
    Coray.schemeModuleHomBaseSmul (ambientToBase (R := K) (σ := Fin 4))
        c (𝟙 (sheafOfModules PS m)) =
      mulHomogeneous PS (p3ScalarHomogeneous K c) m := by
  apply Coray.schemeModuleHom_ext_sections
  intro U s
  rw [Coray.schemeModuleHomBaseSmul_apply]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  apply Subtype.ext
  funext x
  change ((schemeOpenBaseRingHom (ambientToBase (R := K) (σ := Fin 4)) U c).1 x).val *
      s.1 x =
    algebraMap (MvPolynomial (Fin 4) K) (Fiber PS x.1) (MvPolynomial.C c) * s.1 x
  rw [p3AmbientOpenBaseScalar_value K c U x]

/-- Every actual residue coefficient scales under the actual constant
polynomial cochain map; no scalar structure on intrinsic H³ is used here. -/
theorem p3NegativeTwistRawTopResidueCoordinates_scalar_multiplication
    (m : ℕ) (c : K) (w : P3RawTopCocycle K m) :
    p3NegativeTwistRawTopResidueCoordinates K m
        (p3RawTopCocycleMultiply K m 0 (p3ScalarHomogeneous K c) w) =
      c • p3NegativeTwistRawTopResidueCoordinates K m w := by
  funext b
  change (p3NegativeTwistCechTermToLaurent K m 3
    ((p3NegativeTwistCechMultiplication K m 0 (p3ScalarHomogeneous K c)).f 3 w.1)
      id).coeff (p3SerreDualExponent b.1) =
    c * (p3NegativeTwistCechTermToLaurent K m 3 w.1 id).coeff (p3SerreDualExponent b.1)
  rw [p3NegativeTwistCechMultiplication_toLaurent K m 0 3 (p3ScalarHomogeneous K c) w.1 id]
  change (polynomialToLaurent (K := K) (MvPolynomial.C c) *
    p3NegativeTwistCechTermToLaurent K m 3 w.1 id).coeff (p3SerreDualExponent b.1) = _
  rw [polynomialToLaurent_C]
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]

/-- Scalar compatibility descends through the actual all-m Cech-to-Ext
surjection and actual coefficient naturality, with no descent premise. -/
theorem p3NegativeTwistAugmentedExtResidueHom_scalar_multiplication
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) (c : K)
    (z : Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS m) 3) :
    p3NegativeTwistAugmentedExtResidueHom K m
        (z.comp (Ext.mk₀ (mulHomogeneous PS (p3ScalarHomogeneous K c) m)) (add_zero 3)) =
      c • p3NegativeTwistAugmentedExtResidueHom K m z := by
  obtain ⟨w, rfl⟩ := p3RawTopCocycleToAugmentedExt_surjective K m z
  have hmul := p3RawTopCocycleToAugmentedExt_mulHomogeneous K m 0 (p3ScalarHomogeneous K c) w
  simp only [Nat.add_zero] at hmul
  rw [hmul, p3NegativeTwistAugmentedExtResidueHom_raw, p3NegativeTwistAugmentedExtResidueHom_raw]
  exact p3NegativeTwistRawTopResidueCoordinates_scalar_multiplication K m c w

/-- The SAME intrinsic residue map evaluates to the SAME actual descended
residue when the actual augmented target is identified with the unit. -/
theorem p3NegativeTwistCohomologyThreeResidueHom_unit_class
    [HasExt.{u} (Proj PS).Modules] (m : ℕ)
    (z : Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS m) 3) :
    p3NegativeTwistCohomologyThreeResidueHom K m
        (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K) z) =
      p3NegativeTwistAugmentedExtResidueHom K m z := by
  change p3NegativeTwistAugmentedExtResidueHom K m
    ((extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)).symm
      (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K) z)) = _
  rw [AddEquiv.symm_apply_apply]

/-- Actual coefficient naturality carries constant multiplication to the
SAME intrinsic H³ residue, without changing any intrinsic scalar action. -/
theorem p3NegativeTwistCohomologyThreeResidueHom_scalar_multiplication
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) (c : K)
    (z : schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 3) :
    p3NegativeTwistCohomologyThreeResidueHom K m
        (z.comp (Ext.mk₀ (mulHomogeneous PS (p3ScalarHomogeneous K c) m)) (add_zero 3)) =
      c • p3NegativeTwistCohomologyThreeResidueHom K m z := by
  let E : Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS m) 3 ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 3 :=
    extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)
  obtain ⟨a, rfl⟩ := E.surjective z
  have h := extPrecompIsoOfIso_postcomp (p3SectionRepresenterCechTargetIsoUnit K) a
    (mulHomogeneous PS (p3ScalarHomogeneous K c) m)
  calc
    _ = p3NegativeTwistCohomologyThreeResidueHom K m
        (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)
          (a.comp (Ext.mk₀ (mulHomogeneous PS (p3ScalarHomogeneous K c) m)) (add_zero 3))) :=
      congrArg (p3NegativeTwistCohomologyThreeResidueHom K m) h
    _ = _ := by
      rw [p3NegativeTwistCohomologyThreeResidueHom_unit_class,
        p3NegativeTwistCohomologyThreeResidueHom_unit_class]
      exact p3NegativeTwistAugmentedExtResidueHom_scalar_multiplication K m c a

/-- The independently ORIGINAL ambient pi-induced Ext scalar acts on the
SAME residue map by the ordinary ORIGINAL K coordinate scalar. -/
theorem p3NegativeTwistCohomologyThreeResidueHom_smul
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) (c : K) :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    ∀ z : schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 3,
      p3NegativeTwistCohomologyThreeResidueHom K m (c • z) =
        c • p3NegativeTwistCohomologyThreeResidueHom K m z := by
  letI : Linear K (Proj PS).Modules :=
    Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  intro z
  rw [Coray.schemeModuleExt_smul_eq_actual_postcomp
    (ambientToBase (R := K) (σ := Fin 4)) z c,
    p3NegativeTwist_scalarEndomorphism_eq_mulHomogeneous K m c]
  exact p3NegativeTwistCohomologyThreeResidueHom_scalar_multiplication K m c z

/-- The SAME additive intrinsic residue injection with its now PROVED
linearity for the independent ambient base action. No transported action. -/
def p3NegativeTwistCohomologyThreeResidueLinearMap
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 3 →ₗ[K]
      (P3TopResidueExponent m → K) := by
  letI : Linear K (Proj PS).Modules :=
    Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  exact
    { toFun := p3NegativeTwistCohomologyThreeResidueHom K m
      map_add' := (p3NegativeTwistCohomologyThreeResidueHom K m).map_add
      map_smul' := p3NegativeTwistCohomologyThreeResidueHom_smul K m }

/-- Literal equality of the underlying maps; the original residue injection
is enriched with linearity, never replaced by another comparison. -/
theorem p3NegativeTwistCohomologyThreeResidueLinearMap_toAddMonoidHom
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    (p3NegativeTwistCohomologyThreeResidueLinearMap K m).toAddMonoidHom =
      p3NegativeTwistCohomologyThreeResidueHom K m := rfl

/-- The actual linear residue map is injective by the SAME internally proved
additive injection, with no finiteness or comparison premise. -/
theorem p3NegativeTwistCohomologyThreeResidueLinearMap_injective
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Function.Injective (p3NegativeTwistCohomologyThreeResidueLinearMap K m) := by
  letI : Linear K (Proj PS).Modules :=
    Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  exact p3NegativeTwistCohomologyThreeResidueHom_injective K m

/-- Finite-dimensional SAME intrinsic H³ for EVERY actual negative twist,
over the ORIGINAL ambient base field and independently pi-induced action. -/
theorem p3NegativeTwist_cohomology_three_finite_over_ambient_base
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 3) := by
  letI : Linear K (Proj PS).Modules :=
    Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
  letI : Module.Finite K (P3TopResidueExponent m → K) :=
    p3NegativeTwistResidueCoordinateModule_finite K m
  exact FiniteDimensional.of_injective (p3NegativeTwistCohomologyThreeResidueLinearMap K m)
    (p3NegativeTwistCohomologyThreeResidueLinearMap_injective K m)

/-- Primitive ambient caller: native module-sheaf enough-injectives and
HasExt are discharged internally. Only the original Field K and m remain. -/
theorem p3NegativeTwist_cohomology_three_finite_over_ambient_base_native (m : ℕ) :
    letI : EnoughInjectives (Proj PS).Modules :=
      sheafOfModules_enoughInjectives (Proj PS).ringCatSheaf
    letI : HasExt.{u} (Proj PS).Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (Proj PS).Modules
    letI : Linear K (Proj PS).Modules :=
      Coray.schemeModulesLinearOver (ambientToBase (R := K) (σ := Fin 4))
    Module.Finite K (schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 3) := by
  letI : EnoughInjectives (Proj PS).Modules :=
    sheafOfModules_enoughInjectives (Proj PS).ringCatSheaf
  letI : HasExt.{u} (Proj PS).Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (Proj PS).Modules
  exact p3NegativeTwist_cohomology_three_finite_over_ambient_base K m

end PfaffianDescent.ProjectiveNegativeTwist

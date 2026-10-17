import PfaffianDescent.CorayNormalizationDefectNativeLocalization
import PfaffianDescent.CorayGenericNormalizationQuotientSheaf
import PfaffianDescent.SchemeModuleOriginalBaseStalkResidueTower

/-! Actual affine-section defect localized directly into the OWN native stalk
of the SAME integral scheme, inside its SAME function field. This is the
algebra half of D1, not an asserted comparison with the sheaf quotient stalk.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors
attribute [local instance] LocalizedModule.moduleOfIsLocalization
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- All localizations and the common fraction field are derived from the
actual affine neighborhood and actual point. No desired local equivalence
or normalization-defect dimension is a hypothesis. -/
def genericNormalizationDefect_affineNativeLocalizationEquiv
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U)
    (x : U) :
    letI : Nonempty U := ⟨x⟩
    let J := (hU.primeIdealOf x).asIdeal
    letI : J.IsPrime := (hU.primeIdealOf x).isPrime
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf x
    letI : IsLocalization.AtPrime (X.presheaf.stalk x) J := hU.isLocalization_stalk x
    LocalizedModule J.primeCompl (localNormalizationDefect Γ(X, U) X.functionField) ≃ₗ[X.presheaf.stalk x]
      localNormalizationDefect (X.presheaf.stalk x) X.functionField := by
  letI : Nonempty U := ⟨x⟩
  let J := (hU.primeIdealOf x).asIdeal
  letI : J.IsPrime := (hU.primeIdealOf x).isPrime
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) J := hU.isLocalization_stalk x
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
    functionField_isScalarTower X U x
  exact normalizationDefectLocalizationEquiv_native_commonField
    Γ(X, U) (X.presheaf.stalk x) X.functionField J.primeCompl
    J.primeCompl_le_nonZeroDivisors

/-- The SAME actual native localization equivalence, restricted along the
original pi-induced stalk constants. These K actions are specified directly
by the original map, never transported through the equivalence. -/
def genericNormalizationDefect_affineNativeLocalizationGroundEquiv
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (hU : IsAffineOpen U) (x : U) :
    letI : Nonempty U := ⟨x⟩
    let J := (hU.primeIdealOf x).asIdeal
    letI : J.IsPrime := (hU.primeIdealOf x).isPrime
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf x
    letI : IsLocalization.AtPrime (X.presheaf.stalk x) J := hU.isLocalization_stalk x
    letI : Module K (LocalizedModule J.primeCompl (localNormalizationDefect Γ(X, U) X.functionField)) :=
      Module.compHom _ (schemeStalkBaseRingHom pi x)
    letI : Module K (localNormalizationDefect (X.presheaf.stalk x) X.functionField) :=
      Module.compHom _ (schemeStalkBaseRingHom pi x)
    LocalizedModule J.primeCompl (localNormalizationDefect Γ(X, U) X.functionField) ≃ₗ[K]
      localNormalizationDefect (X.presheaf.stalk x) X.functionField := by
  letI : Nonempty U := ⟨x⟩
  let J := (hU.primeIdealOf x).asIdeal
  letI : J.IsPrime := (hU.primeIdealOf x).isPrime
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf x
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) J := hU.isLocalization_stalk x
  letI : Module K (LocalizedModule J.primeCompl (localNormalizationDefect Γ(X, U) X.functionField)) :=
    Module.compHom _ (schemeStalkBaseRingHom pi x)
  letI : Module K (localNormalizationDefect (X.presheaf.stalk x) X.functionField) :=
    Module.compHom _ (schemeStalkBaseRingHom pi x)
  let e := genericNormalizationDefect_affineNativeLocalizationEquiv X U hU x
  refine
    { toAddEquiv := e.toAddEquiv
      map_smul' := ?_ }
  intro c m
  exact e.map_smul (schemeStalkBaseRingHom pi x c) m

end PfaffianDescent.Coray

import PfaffianDescent.SchemeModuleOpenImmersionNativeStalkLinear
import PfaffianDescent.CorayGenericNormalizationQuotientFromSpecTilde
import PfaffianDescent.CorayNormalizationDefectNativeLocalization
import PfaffianDescent.SchemeModuleOriginalBaseWeightedStalk

/-! D1: the ACTUAL normalization quotient's own native stalk is the SAME
local normalization defect, with its native local-ring and original K actions.
SOURCE ONLY / UNVERIFIED. Root alone compiles. No desired Iso is supplied.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The original chart's scalar germ is carried to the canonical Spec stalk
scalar by its ACTUAL fromSpec stalk map. -/
theorem affineFromSpec_stalkMap_section_germ
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (y : Spec Γ(X, U)) (hy : hU.fromSpec y ∈ U) (a : Γ(X, U)) :
    hU.fromSpec.stalkMap y
        (X.presheaf.germ U (hU.fromSpec y) hy a) =
      StructureSheaf.toStalk Γ(X, U) y a := by
  rw [Scheme.Hom.germ_stalkMap_apply, hU.fromSpec_app_self]
  change (Spec Γ(X, U)).presheaf.germ (hU.fromSpec ⁻¹ᵁ U) y hy
      ((Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op
        ((Scheme.ΓSpecIso Γ(X, U)).inv a)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

/-- Genuine native-stalk normalization defect comparison at an actual chart
point. The source is the original quotient sheaf's own stalk. The R action
is its independently native action; the chart germ and SAME function field
provide all localization hypotheses internally. -/
def genericNormalizationQuotientSheaf_fromSpecNativeStalkDefectEquiv
    (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) (hU : IsAffineOpen U) (y : Spec Γ(X, U)) :
    letI := schemeModuleStalkModule (genericNormalizationQuotientSheaf X) (hU.fromSpec y)
    (genericNormalizationQuotientSheaf X).presheaf.stalk (hU.fromSpec y) ≃ₗ[
      X.presheaf.stalk (hU.fromSpec y)]
      localNormalizationDefect (X.presheaf.stalk (hU.fromSpec y)) X.functionField := by
  let f := hU.fromSpec
  have hy : f y ∈ U := by
    have hyRange : f y ∈ hU.fromSpec.opensRange := ⟨y, rfl⟩
    exact (congrArg (fun V : X.Opens => f y ∈ V)
      hU.opensRange_fromSpec).mp hyRange
  let xU : U := ⟨f y, hy⟩
  letI : Nonempty U := ⟨xU⟩
  let A := Γ(X, U)
  let Rf := X.presheaf.stalk (f y)
  let Rs := (Spec A).presheaf.stalk y
  let D := localNormalizationDefect A X.functionField
  letI : y.asIdeal.IsPrime := y.isPrime
  let Q := genericNormalizationQuotientSheaf X
  let T := tilde (R := CommRingCat.of A) (ModuleCat.of A D)
  letI : Algebra A Rf := TopCat.Presheaf.algebra_section_stalk X.presheaf xU
  letI : Algebra A Rs := (StructureSheaf.toStalk A y).hom.toAlgebra
  letI : IsLocalization.AtPrime Rf y.asIdeal := hU.isLocalization_stalk' y hy
  letI : IsFractionRing A X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsScalarTower A Rf X.functionField := functionField_isScalarTower X U xU
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  letI : Algebra A
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
    ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
  letI := schemeModuleStalkModule Q (f y)
  letI := schemeModuleStalkModule (Q.restrict f) y
  letI := schemeModuleStalkModule T y
  letI : Module A (Q.presheaf.stalk (f y)) :=
    Module.compHom _ (algebraMap A Rf)
  letI : Module A ((Q.restrict f).presheaf.stalk y) :=
    Module.compHom _ (algebraMap A Rs)
  letI : Module A (T.presheaf.stalk y) :=
    Module.compHom _ (algebraMap A Rs)
  letI : IsScalarTower A Rf (Q.presheaf.stalk (f y)) :=
    IsScalarTower.of_compHom A Rf _
  letI : IsScalarTower A Rs ((Q.restrict f).presheaf.stalk y) :=
    IsScalarTower.of_compHom A Rs _
  letI : IsScalarTower A Rs (T.presheaf.stalk y) :=
    IsScalarTower.of_compHom A Rs _
  let eRes : Q.presheaf.stalk (f y) ≃ₗ[A] (Q.restrict f).presheaf.stalk y :=
    { toAddEquiv := ((Scheme.Modules.restrictStalkNatIso f y).app Q).symm.addCommGroupIsoToAddEquiv
      map_smul' := by
        intro a m
        change (Scheme.Modules.restrictStalkNatIso f y).inv.app Q
            (X.presheaf.germ U (f y) hy a • m) =
          algebraMap A Rs a •
            (show (Q.restrict f).presheaf.stalk y from
              (Scheme.Modules.restrictStalkNatIso f y).inv.app Q m)
        rw [openImmersion_moduleRestrictStalk_inv_smul f y Q]
        rw [affineFromSpec_stalkMap_section_germ X U hU y hy a]
        rfl }
  let eModel : Q.restrict f ≅ T :=
    genericNormalizationQuotientSheaf_fromSpecTildeIso X U hU
  let eModelStalk : (Q.restrict f).presheaf.stalk y ≃ₗ[Rs] T.presheaf.stalk y :=
    ((schemeModuleStalkModuleFunctor (Spec A) y).mapIso eModel).toLinearEquiv
  let eA : Q.presheaf.stalk (f y) ≃ₗ[A] T.presheaf.stalk y :=
    eRes.trans (eModelStalk.restrictScalars A)
  let g : D →ₗ[A] T.presheaf.stalk y := (tilde.toStalk (ModuleCat.of A D) y).hom
  letI : IsLocalizedModule y.asIdeal.primeCompl g := by
    dsimp only [g, T]
    exact tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      (R := CommRingCat.of A) (ModuleCat.of A D) y
  let eLocA : Q.presheaf.stalk (f y) ≃ₗ[A] LocalizedModule y.asIdeal.primeCompl D :=
    eA.trans (IsLocalizedModule.iso y.asIdeal.primeCompl g).symm
  let eLoc : Q.presheaf.stalk (f y) ≃ₗ[Rf] LocalizedModule y.asIdeal.primeCompl D :=
    eLocA.extendScalarsOfIsLocalization y.asIdeal.primeCompl Rf
  exact eLoc.trans (normalizationDefectLocalizationEquiv_native_commonField
    A Rf X.functionField y.asIdeal.primeCompl y.asIdeal.primeCompl_le_nonZeroDivisors)

/-- The same constructed native comparison, restricted to the SAME original
pi-induced K action on the quotient stalk and on the native defect. -/
def genericNormalizationQuotientSheaf_fromSpecNativeStalkDefectGroundEquiv
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (hU : IsAffineOpen U) (y : Spec Γ(X, U)) :
    letI : Module K (localNormalizationDefect
        (X.presheaf.stalk (hU.fromSpec y)) X.functionField) :=
      Module.compHom _ (schemeStalkBaseRingHom pi (hU.fromSpec y))
    SchemeModuleStalkOver pi (genericNormalizationQuotientSheaf X) (hU.fromSpec y) ≃ₗ[K]
      localNormalizationDefect (X.presheaf.stalk (hU.fromSpec y)) X.functionField := by
  letI : Module K (localNormalizationDefect
      (X.presheaf.stalk (hU.fromSpec y)) X.functionField) :=
    Module.compHom _ (schemeStalkBaseRingHom pi (hU.fromSpec y))
  letI := schemeModuleStalkModule (genericNormalizationQuotientSheaf X) (hU.fromSpec y)
  let e := genericNormalizationQuotientSheaf_fromSpecNativeStalkDefectEquiv X U hU y
  refine { toAddEquiv := e.toAddEquiv, map_smul' := ?_ }
  intro c m
  exact e.map_smul (schemeStalkBaseRingHom pi (hU.fromSpec y) c) m

/-- The same actual comparison at the original point of the affine open.
Only equality elimination along the actual fromSpec/primeIdealOf identity
is used; the point and its independently native action remain unchanged. -/
def genericNormalizationQuotientSheaf_affineNativeStalkDefectEquiv
    (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) (hU : IsAffineOpen U) (x : U) :
    letI := schemeModuleStalkModule (genericNormalizationQuotientSheaf X) x.1
    (genericNormalizationQuotientSheaf X).presheaf.stalk x.1 ≃ₗ[
      X.presheaf.stalk x.1] localNormalizationDefect (X.presheaf.stalk x.1) X.functionField := by
  let E (z : X) :=
    letI := schemeModuleStalkModule (genericNormalizationQuotientSheaf X) z
    (genericNormalizationQuotientSheaf X).presheaf.stalk z ≃ₗ[X.presheaf.stalk z]
      localNormalizationDefect (X.presheaf.stalk z) X.functionField
  exact cast (congrArg E (hU.fromSpec_primeIdealOf x))
    (genericNormalizationQuotientSheaf_fromSpecNativeStalkDefectEquiv X U hU
      (hU.primeIdealOf x))

/-- D1 over the original ground field at the original affine-open point.
The target action is restriction of its own native action along the SAME
pi-induced K-to-stalk map, and the source is the original stalk-over-K alias. -/
def genericNormalizationQuotientSheaf_affineNativeStalkDefectGroundEquiv
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (hU : IsAffineOpen U) (x : U) :
    letI : Module K (localNormalizationDefect (X.presheaf.stalk x.1) X.functionField) :=
      Module.compHom _ (schemeStalkBaseRingHom pi x.1)
    SchemeModuleStalkOver pi (genericNormalizationQuotientSheaf X) x.1 ≃ₗ[K]
      localNormalizationDefect (X.presheaf.stalk x.1) X.functionField := by
  letI : Module K (localNormalizationDefect (X.presheaf.stalk x.1) X.functionField) :=
    Module.compHom _ (schemeStalkBaseRingHom pi x.1)
  letI := schemeModuleStalkModule (genericNormalizationQuotientSheaf X) x.1
  let e := genericNormalizationQuotientSheaf_affineNativeStalkDefectEquiv X U hU x
  refine { toAddEquiv := e.toAddEquiv, map_smul' := ?_ }
  intro c m
  exact e.map_smul (schemeStalkBaseRingHom pi x.1 c) m

end PfaffianDescent.Coray

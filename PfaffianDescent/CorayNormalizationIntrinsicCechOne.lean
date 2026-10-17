import PfaffianDescent.SchemeCoverCechExtDegreeOne
import PfaffianDescent.CorayFiniteSchemeGenericNormalization
import PfaffianDescent.AffineOpenCohomology
import PfaffianDescent.SchemeCoverDegreeZeroAcyclic
import PfaffianDescent.SheafModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.AlgebraicGeometry.Noetherian

/-! Genuine intrinsic normalization H¹ through its actual preimage affine
cover. Finite normalization, local Noetherianity, Ext infrastructure and
local Ext¹ are derived internally from characteristic-zero finite-type
geometry. The comparison to ORIGINAL-X pushforward cohomology remains open.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact fromSpec restriction of the actual structure module is QC,
from the genuine restriction/unit isomorphism and the actual Spec tilde unit.
The affine open can be empty. -/
theorem schemeModuleUnit_restrictFromSpec_isQuasicoherent
    (Y : Scheme.{u}) (V : Y.Opens) (hV : IsAffineOpen V) :
    ((Scheme.Modules.restrictFunctor hV.fromSpec).obj
      (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent := by
  have hunit : (SheafOfModules.unit (Spec Γ(Y, V)).ringCatSheaf).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec Γ(Y, V)).ringCatSheaf).prop_of_iso
    (Scheme.Modules.restrictUnitIso hV.fromSpec).symm hunit

/-- The actual preimages of all actual affine opens cover the actual
normalization. The covering identity is pulled back, not supplied. -/
theorem genericNormalization_preimageAffineOpenFamily_coversTop
    (X : Scheme.{u}) [IsIntegral X] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    (Opens.grothendieckTopology (X.fromSpecStalk (genericPoint X)).normalization).CoversTop
      (fun i : X.affineOpens => (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ i.1) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  apply (Opens.coversTop_iff _ (fun i : X.affineOpens => ν ⁻¹ᵁ i.1)).mpr
  exact ν.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)

/-- The genuine intrinsic H¹ of the actual finite normalization is the
quotient of genuine degree-one cocycles on the actual preimage affine cover.
Only ordinary original characteristic-zero finite-type geometry is an input.
Finite normalization, Noetherianity, enough injectives, HasExt, cover,
local QC, local Ext¹ and actual degree-zero coproduct Ext¹ are all internal.
This does not identify this quotient with the ORIGINAL-X quotient. -/
def genericNormalizationUnit_preimageAffineCechQuotientEquivCohomologyOne
    {K : Type u} [Field K] [CharZero K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    let V : X.affineOpens → N.Opens := fun i => (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ i.1
    let M : N.Modules := SheafOfModules.unit N.ringCatSheaf
    DegreeOneCocycle ((sectionRepresenterCechChain N.ringCatSheaf V).d 2 1) (Y := M) ⧸
        (schemeCoverDegreeOneToExtHom V (genericNormalization_preimageAffineOpenFamily_coversTop X) M).ker ≃+
      schemeModuleCohomology N M 1 := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsFinite ν := integralScheme_genericNormalization_isFinite X pi
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  letI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian ν
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  let V : X.affineOpens → N.Opens := fun i => ν ⁻¹ᵁ i.1
  let M : N.Modules := SheafOfModules.unit N.ringCatSheaf
  letI : ∀ i, Subsingleton (Ext.{u} (C := N.Modules)
      (show N.Modules from sectionRepresenter N.ringCatSheaf (V i)) M 1) := fun i =>
    (sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen_of_restrict
      (V i) (i.2.preimage ν) M
      (schemeModuleUnit_restrictFromSpec_isQuasicoherent N (V i) (i.2.preimage ν))).1
  letI : Subsingleton (Ext.{u} (C := N.Modules)
      (show N.Modules from (sectionRepresenterCechChain N.ringCatSheaf V).X 0) M 1) :=
    schemeCover_degree_zero_ext_one_subsingleton V M
  exact schemeCoverDegreeOneQuotientEquivCohomologyOne V
    (genericNormalization_preimageAffineOpenFamily_coversTop X) M

end PfaffianDescent.Coray

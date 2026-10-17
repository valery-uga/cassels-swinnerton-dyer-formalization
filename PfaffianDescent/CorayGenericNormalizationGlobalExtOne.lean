import PfaffianDescent.CorayGenericNormalizationAffineExtVanishing
import PfaffianDescent.CorayClosedSupportCechExtOneIntegration
import PfaffianDescent.SchemeCoverDegreeZeroAcyclic
import PfaffianDescent.SchemeModuleCohomology

/-! Actual degree-zero coproduct Ext and global normalization-quotient H¹.
Local quasicoherence and Ext, image exactness, and covering augmentation
are derived from actual constructions. The generic global theorem retains
only natural closed-support-contained-in-affine geometry.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ACTUAL degree-zero term for any family of ACTUAL affine opens has
vanishing Ext¹ into the ACTUAL canonical normalization quotient. The family
need not be finite or cover X; every local Ext input is derived from QC. -/
theorem genericNormalizationQuotientSheaf_affineFamily_degreeZeroExt_one_subsingleton
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [hExt : HasExt.{u} X.Modules] {ι : Type u}
    (W : ι → X.Opens) (hW : ∀ i, IsAffineOpen (W i)) :
    Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf W).X 0)
      (genericNormalizationQuotientSheaf X) 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : ∀ i, Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from sectionRepresenter X.ringCatSheaf (W i))
      (genericNormalizationQuotientSheaf X) 1) := fun i =>
    (genericNormalizationQuotientSheaf_affine_sectionRepresenter_ext_one_and_two_subsingleton
      X (W i) (hW i)).1
  exact schemeCover_degree_zero_ext_one_subsingleton W
    (genericNormalizationQuotientSheaf X)

/-- Genuine unit Ext¹, equivalently degree-one scheme-module cohomology,
vanishes for the ACTUAL global normalization quotient when its ACTUAL stalk
support is closed and contained in an ACTUAL affine open. The canonical
family of all affine opens supplies the cover internally. No QC, local Ext,
degree-zero Ext, image, augmentation, or comparison certificate is an input. -/
theorem genericNormalizationQuotientSheaf_cohomology_one_subsingleton_of_closedSupport_subset_affine
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (hclosed : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)))
    (U : X.Opens) (hU : IsAffineOpen U)
    (hsU : schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U) :
    Subsingleton (schemeModuleCohomology X (genericNormalizationQuotientSheaf X) 1) := by
  let Q := genericNormalizationQuotientSheaf X
  let V : X.affineOpens → X.Opens := fun i => i.1
  have hV : ⊤ ≤ ⨆ i, V i := by
    change ⊤ ≤ ⨆ i : X.affineOpens, (i : X.Opens)
    exact (iSup_affineOpens_eq_top X).ge
  let A := supportAugmentedOpenFamily U V
  have hA : ∀ a : Option X.affineOpens, IsAffineOpen (A a) := by
    intro a
    cases a with
    | none =>
        change IsAffineOpen U
        exact hU
    | some i =>
        change IsAffineOpen (i : X.Opens)
        exact i.2
  have hDegreeZeroExt : Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf A).X 0) Q 1) :=
    genericNormalizationQuotientSheaf_affineFamily_degreeZeroExt_one_subsingleton A hA
  change Subsingleton (Ext.{u} (C := X.Modules)
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) Q 1)
  exact schemeModule_unit_ext_one_subsingleton_of_closedSupport_of_degreeZeroExt
    pi Q U V hV (schemeModuleStalkSupport Q) hclosed (Set.Subset.rfl) hsU hDegreeZeroExt

end PfaffianDescent.Coray

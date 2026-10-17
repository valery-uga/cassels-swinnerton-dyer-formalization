import PfaffianDescent.AffineOpenCohomology
import PfaffianDescent.CorayClosedSupportCechExtOneIntegration
import PfaffianDescent.SchemeCoverDegreeZeroAcyclic
import PfaffianDescent.SchemeModuleCohomology

/-! Genuine H1 vanishing for the SAME quasicoherent coefficient whose OWN
closed support is contained in an affine open. No normalization quotient
substitution and no external Ext vanishing certificate.
SOURCE ONLY / UNVERIFIED. Root alone compiles and audits. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Closed support inside one affine open makes genuine unit Ext1 vanish
for the actual quasicoherent module. The canonical family of all affine
opens supplies a cover; affine QC vanishing supplies the degree-zero Ext
input to the existing supported Cech contraction. -/
theorem schemeModule_quasicoherent_cohomology_one_subsingleton_of_closedSupport_subset_affine
    {K : Type u} [Field K] {X : Scheme.{u}} [IsLocallyNoetherian X]
    [hExt : HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) [M.IsQuasicoherent]
    (hclosed : IsClosed (schemeModuleStalkSupport M))
    (U : X.Opens) (hU : IsAffineOpen U)
    (hsU : schemeModuleStalkSupport M ⊆ U) :
    Subsingleton (schemeModuleCohomology X M 1) := by
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
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  letI : ∀ a, Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from sectionRepresenter X.ringCatSheaf (A a)) M 1) := fun a =>
    (sectionRepresenter_ext_one_and_two_subsingleton_of_isAffineOpen (A a) (hA a) M).1
  have hDegreeZeroExt : Subsingleton (Ext.{u} (C := X.Modules)
      (show X.Modules from (sectionRepresenterCechChain X.ringCatSheaf A).X 0) M 1) :=
    schemeCover_degree_zero_ext_one_subsingleton A M
  change Subsingleton (Ext.{u} (C := X.Modules)
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) M 1)
  exact schemeModule_unit_ext_one_subsingleton_of_closedSupport_of_degreeZeroExt
    pi M U V hV (schemeModuleStalkSupport M) hclosed Set.Subset.rfl hsU hDegreeZeroExt

end PfaffianDescent.Coray

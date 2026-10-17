import PfaffianDescent.LocalExtResidueInjective
import PfaffianDescent.SchemeModuleCohomology
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! Positive cohomology of an ACTUAL sheaf module supported at a closed
point. The genuine stalk--skyscraper derived adjunction and actual unit-stalk
Iso reduce the result to projectivity of the local ring over itself.
No quasicoherence, affine acyclicity, finite length or Ext-vanishing premise.
SOURCE ONLY / UNVERIFIED. Root owns all compiler checks. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine stalk functor sends the ACTUAL scheme-module unit to a
projective object: its canonical local-ring comparison is used, rather
than renaming the stalk or assuming a projective stalk. -/
theorem schemeModuleUnitStalk_projective (X : Scheme.{u}) (x : X) :
    Projective ((schemeModuleStalkModuleFunctor X x).obj
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :=
  Projective.of_iso (schemeModuleUnitStalkIso X x).symm inferInstance

/-- Positive unit Ext into the ACTUAL skyscraper vanishes. Native local
HasExt infrastructure is constructed internally, at the universe required
by the existing genuine derived stalk--skyscraper adjunction. -/
theorem schemeModuleSkyscraper_cohomology_succ_subsingleton
    {X : Scheme.{u}} [HasExt.{u} X.Modules] (x : X)
    (hx : IsClosed ({x} : Set X))
    (A : ModuleCat.{u} (X.presheaf.stalk x)) (n : ℕ) :
    Subsingleton (schemeModuleCohomology X (schemeModuleSkyscraper x A) (n + 1)) := by
  letI : EnoughInjectives (ModuleCat.{u} (X.presheaf.stalk x)) :=
    @ModuleCat.enoughInjectives.{u, u} (X.presheaf.stalk x) inferInstance
  letI : HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x)) :=
    CategoryTheory.hasExt_of_enoughInjectives.{u + 1, u, u + 1}
      (ModuleCat.{u} (X.presheaf.stalk x))
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  letI : Projective ((schemeModuleStalkModuleFunctor X x).obj O) :=
    schemeModuleUnitStalk_projective X x
  letI : Subsingleton
      (Ext.{u + 1} ((schemeModuleStalkModuleFunctor X x).obj O) A (n + 1)) :=
    Ext.subsingleton_of_projective _ _ n
  constructor
  intro a b
  apply (schemeModuleStalkSkyscraperExtMap_bijective x hx O A (n + 1)).1
  exact Subsingleton.elim _ _

/-- A sheaf module supported at one ACTUAL closed point has zero positive
cohomology. Its actual map to the skyscraper of its own stalk is proved
invertible by the existing off-support theorem, with no comparison input. -/
theorem schemeModuleCohomology_succ_subsingleton_of_closedPoint_support
    {X : Scheme.{u}} [HasExt.{u} X.Modules] (x : X)
    (hx : IsClosed ({x} : Set X)) (M : X.Modules)
    (hM : ∀ y : X, y ≠ x → Subsingleton (M.presheaf.stalk y)) (n : ℕ) :
    Subsingleton (schemeModuleCohomology X M (n + 1)) := by
  let A := (schemeModuleStalkModuleFunctor X x).obj M
  let eta := schemeModuleToSkyscraper x (𝟙 A)
  letI : IsIso eta := schemeModuleToSkyscraper_isIso_of_subsingleton_off x M hx hM
  letI : Subsingleton (schemeModuleCohomology X (schemeModuleSkyscraper x A) (n + 1)) :=
    schemeModuleSkyscraper_cohomology_succ_subsingleton x hx A n
  exact ext_subsingleton_of_iso_right (asIso eta).symm (n + 1)

/-- In particular, the pushforward of ANY actual module on the SAME
residue-field point has zero positive cohomology. Its support condition
and closed-immersion structure are discharged internally. This applies
directly to i_*i^*D, without replacing its intrinsic fiber by bare κ(P). -/
theorem schemeModuleResiduePointPushforward_cohomology_succ_subsingleton
    {X : Scheme.{u}} [HasExt.{u} X.Modules] (P : closedPoints X)
    (A : (Spec (X.residueField P.1)).Modules) (n : ℕ) :
    Subsingleton (schemeModuleCohomology X
      ((Scheme.Modules.pushforward (X.fromSpecResidueField P.1)).obj A) (n + 1)) := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  apply schemeModuleCohomology_succ_subsingleton_of_closedPoint_support P.1 P.2
    ((Scheme.Modules.pushforward i).obj A) _ n
  intro y hy
  apply schemeModulePushforward_stalk_subsingleton_off_range i A y
  rintro ⟨z, hz⟩
  exact hy (hz.symm.trans (Scheme.fromSpecResidueField_apply P.1 z))

end PfaffianDescent

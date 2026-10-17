import PfaffianDescent.ExactRightAdjointExtOneInjection
import PfaffianDescent.ClosedImmersionPushforwardExact
import PfaffianDescent.CorayPushforwardCechGroundLinearity
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! SOURCE ONLY / UNVERIFIED. Intrinsic degree-one cohomology injects into
actual closed-immersion pushforward cohomology, linearly over the ORIGINAL
base field. The two category actions are constructed independently from pi
and f >> pi. Pullback is never asserted exact or injective-preserving. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine pushforward linearity for the two independent original actions.
The actual scalar restriction uses f.app and the proved original constant
formula. No action is defined by transport through a comparison. -/
def schemeModulePushforward_linearOver
    (pi : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) :
    letI : Linear K Y.Modules := schemeModulesLinearOver pi
    letI : Linear K X.Modules := schemeModulesLinearOver (f ≫ pi)
    (Scheme.Modules.pushforward f).Linear K := by
  letI : Linear K Y.Modules := schemeModulesLinearOver pi
  letI : Linear K X.Modules := schemeModulesLinearOver (f ≫ pi)
  refine ⟨?_⟩
  intro M N h c
  apply schemeModuleHom_ext_sections
  intro U s
  change schemeOpenBaseRingHom (f ≫ pi) (f ⁻¹ᵁ U) c •
      h.val.app (op (f ⁻¹ᵁ U)) s =
    f.app U (schemeOpenBaseRingHom pi U c) • h.val.app (op (f ⁻¹ᵁ U)) s
  rw [schemeOpenBaseRingHom_pullback]

/-- The actual degree-one map: first precompose by the genuine pullback-unit
isomorphism, then apply the exact right-adjoint Ext map. All scalar structures
are the installed Ext structures from the independently given base actions. -/
def closedImmersion_cohomologyOneLinearMap
    (pi : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [IsClosedImmersion f]
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] (M : X.Modules) :
    letI : Linear K Y.Modules := schemeModulesLinearOver pi
    letI : Linear K X.Modules := schemeModulesLinearOver (f ≫ pi)
    schemeModuleCohomology X M 1 →ₗ[K]
      schemeModuleCohomology Y ((Scheme.Modules.pushforward f).obj M) 1 := by
  letI : Linear K Y.Modules := schemeModulesLinearOver pi
  letI : Linear K X.Modules := schemeModulesLinearOver (f ≫ pi)
  let F := Scheme.Modules.pullback f
  let G := Scheme.Modules.pushforward f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  letI : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (SheafOfModules.pushforward f.toRingCatSheafHom)
    exact SheafOfModules.pushforward_preservesFiniteLimits _
  letI : G.Additive := Functor.additive_of_preserves_binary_products G
  letI : G.Linear K := schemeModulePushforward_linearOver pi f
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison f) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  let e := asIso (BundleSectionZeroLocus.pullbackUnitComparison f)
  exact (rightAdjointExtLinearMap K F G adj
      (SheafOfModules.unit Y.ringCatSheaf) M 1).comp
    ((Ext.mk₀ e.hom).precompOfLinear K M (zero_add 1))

/-- No cohomology injection or acyclicity certificate is supplied. Exactness
of the actual closed pushforward and the original pullback-unit Iso discharge
the generic presentation argument. Enough injectives is constructed locally. -/
theorem closedImmersion_cohomologyOneLinearMap_injective
    (pi : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [IsClosedImmersion f]
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] (M : X.Modules) :
    Function.Injective (closedImmersion_cohomologyOneLinearMap pi f M) := by
  letI : Linear K Y.Modules := schemeModulesLinearOver pi
  letI : Linear K X.Modules := schemeModulesLinearOver (f ≫ pi)
  let F := Scheme.Modules.pullback f
  let G := Scheme.Modules.pushforward f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  letI : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (SheafOfModules.pushforward f.toRingCatSheafHom)
    exact SheafOfModules.pushforward_preservesFiniteLimits _
  letI : G.Additive := Functor.additive_of_preserves_binary_products G
  letI : G.Linear K := schemeModulePushforward_linearOver pi f
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison f) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  let e := asIso (BundleSectionZeroLocus.pullbackUnitComparison f)
  have hSource : Function.Injective
      ((Ext.mk₀ e.hom).precompOfLinear K M (zero_add 1)) := by
    intro a b hab
    have h := congrArg (fun z => (Ext.mk₀ e.inv).comp z (zero_add 1)) hab
    change (Ext.mk₀ e.inv).comp
        ((Ext.mk₀ e.hom).comp a (zero_add 1)) (zero_add 1) =
      (Ext.mk₀ e.inv).comp
        ((Ext.mk₀ e.hom).comp b (zero_add 1)) (zero_add 1) at h
    simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp] using h
  change Function.Injective
    ((rightAdjointExtLinearMap K F G adj (SheafOfModules.unit Y.ringCatSheaf) M 1).comp
      ((Ext.mk₀ e.hom).precompOfLinear K M (zero_add 1)))
  exact (rightAdjointExtLinearMap_one_injective K F G adj
    (SheafOfModules.unit Y.ringCatSheaf) M).comp hSource

/-- Finite ORIGINAL-K ambient H1 bounds intrinsic H1 through the genuine
original-K injection. Neither scalar action is transported to make this true. -/
theorem closedImmersion_cohomology_one_finite_of_pushforward
    (pi : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [IsClosedImmersion f]
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] (M : X.Modules) :
    letI : Linear K Y.Modules := schemeModulesLinearOver pi
    letI : Linear K X.Modules := schemeModulesLinearOver (f ≫ pi)
    Module.Finite K (schemeModuleCohomology Y ((Scheme.Modules.pushforward f).obj M) 1) →
      Module.Finite K (schemeModuleCohomology X M 1) := by
  letI : Linear K Y.Modules := schemeModulesLinearOver pi
  letI : Linear K X.Modules := schemeModulesLinearOver (f ≫ pi)
  intro hfinite
  letI := hfinite
  exact Module.Finite.of_injective (closedImmersion_cohomologyOneLinearMap pi f M)
    (closedImmersion_cohomologyOneLinearMap_injective pi f M)

end PfaffianDescent.Coray

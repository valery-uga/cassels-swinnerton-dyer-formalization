import PfaffianDescent.ExactRightAdjointExtOneSurjection
import PfaffianDescent.ClosedImmersionCohomologyOneLinearInjection
import PfaffianDescent.SheafModuleFlasque

/-! SOURCE ONLY / UNVERIFIED160. The SAME existing closed-immersion
intrinsic-to-ambient H¹ map is surjective, hence an equivalence over the
independently constructed original field actions. Its image-of-injective
acyclicity is produced internally using native flasque sheaf theory. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pushforward retains the SAME underlying additive presheaf, so native
additive flasqueness survives every scheme morphism. -/
theorem schemeModulePushforward_isFlasque
    (f : X ⟶ Y) (M : X.Modules)
    [TopCat.Presheaf.IsFlasque M.val.presheaf] :
    TopCat.Presheaf.IsFlasque
      ((Scheme.Modules.pushforward f).obj M).val.presheaf :=
  TopCat.Presheaf.IsFlasque.pushforward_isFlasque M.val.presheaf f.base

/-- Every intrinsic injective has ambient H¹-acyclic pushforward. No
preservation of injective objects is claimed or needed. -/
theorem schemeModulePushforward_injective_cohomology_one_subsingleton
    (f : X ⟶ Y) [HasExt.{u} Y.Modules] (I : X.Modules) [Injective I] :
    Subsingleton (schemeModuleCohomology Y
      ((Scheme.Modules.pushforward f).obj I) 1) := by
  letI : EnoughInjectives Y.Modules := sheafOfModules_enoughInjectives Y.ringCatSheaf
  letI : TopCat.Presheaf.IsFlasque I.val.presheaf := injective_isFlasque_scheme X I
  letI : TopCat.Presheaf.IsFlasque
      ((Scheme.Modules.pushforward f).obj I).val.presheaf :=
    schemeModulePushforward_isFlasque f I
  exact flasque_schemeModuleCohomology_one Y ((Scheme.Modules.pushforward f).obj I)

/-- Surjectivity of the SAME accepted original-field linear H¹ map.
Enough injectives and the needed single injective-image acyclicity are
constructed inside the proof; no comparison or acyclicity certificate input. -/
theorem closedImmersion_cohomologyOneLinearMap_surjective
    (pi : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [IsClosedImmersion f]
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] (M : X.Modules) :
    Function.Surjective (closedImmersion_cohomologyOneLinearMap pi f M) := by
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
  let I : InjectivePresentation M := Classical.arbitrary _
  letI : Injective I.J := I.injective
  have hAcyclic : Subsingleton (schemeModuleCohomology Y (G.obj I.J) 1) :=
    schemeModulePushforward_injective_cohomology_one_subsingleton f I.J
  have hRight : Function.Surjective (rightAdjointExtLinearMap K F G adj
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) M 1) :=
    rightAdjointExtLinearMap_one_surjective_of_presentation K F G adj
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) M I hAcyclic
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison f) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  let e := asIso (BundleSectionZeroLocus.pullbackUnitComparison f)
  have hLeft : Function.Surjective
      ((Ext.mk₀ e.hom).precompOfLinear K M (zero_add 1)) := by
    intro z
    refine ⟨(Ext.mk₀ e.inv).comp z (zero_add 1), ?_⟩
    change (Ext.mk₀ e.hom).comp
      ((Ext.mk₀ e.inv).comp z (zero_add 1)) (zero_add 1) = z
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  change Function.Surjective
    ((rightAdjointExtLinearMap K F G adj
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) M 1).comp
      ((Ext.mk₀ e.hom).precompOfLinear K M (zero_add 1)))
  exact hRight.comp hLeft

/-- The native closed-immersion H¹ map is bijective, with its original
scalars and actual pushforward coefficient sheaf. -/
theorem closedImmersion_cohomologyOneLinearMap_bijective
    (pi : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [IsClosedImmersion f]
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] (M : X.Modules) :
    Function.Bijective (closedImmersion_cohomologyOneLinearMap pi f M) :=
  ⟨closedImmersion_cohomologyOneLinearMap_injective pi f M,
    closedImmersion_cohomologyOneLinearMap_surjective pi f M⟩

/-- Original-field intrinsic/ambient H¹ comparison, constructed from the
SAME map rather than defining either scalar action by transport. -/
def closedImmersion_cohomologyOneLinearEquiv
    (pi : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [IsClosedImmersion f]
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] (M : X.Modules) :
    letI : Linear K Y.Modules := schemeModulesLinearOver pi
    letI : Linear K X.Modules := schemeModulesLinearOver (f ≫ pi)
    schemeModuleCohomology X M 1 ≃ₗ[K]
      schemeModuleCohomology Y ((Scheme.Modules.pushforward f).obj M) 1 := by
  letI : Linear K Y.Modules := schemeModulesLinearOver pi
  letI : Linear K X.Modules := schemeModulesLinearOver (f ≫ pi)
  exact LinearEquiv.ofBijective (closedImmersion_cohomologyOneLinearMap pi f M)
    (closedImmersion_cohomologyOneLinearMap_bijective pi f M)

/-- The new equivalence retains the actual comparison map. -/
theorem closedImmersion_cohomologyOneLinearEquiv_apply
    (pi : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [IsClosedImmersion f]
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules] (M : X.Modules)
    (z : schemeModuleCohomology X M 1) :
    closedImmersion_cohomologyOneLinearEquiv pi f M z =
      closedImmersion_cohomologyOneLinearMap pi f M z := rfl

end PfaffianDescent.Coray

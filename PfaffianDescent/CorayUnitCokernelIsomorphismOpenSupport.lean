import PfaffianDescent.CorayOpenRestrictPushforwardUnit
import PfaffianDescent.CorayAffineSourceSpecTransport
import PfaffianDescent.CorayActualStalkSupportTransport
import PfaffianDescent.CorayNativeStalkCokernelZero

/-! An actual isomorphism locus annihilates the actual unit-cokernel stalks.
The geometric construction of this locus is a separate theorem. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- For any scheme morphism, its actual unit cokernel is supported outside
any open on which the SAME morphism is an isomorphism. -/
theorem unitCokernelSheaf_stalkSupport_subset_compl_of_restrict_isIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] :
    schemeModuleStalkSupport
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ⊆
        (U : Set X)ᶜ := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let qU := SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom
  let ePush := openRestrictPushforwardUnitIso f U
  let eUnit := Scheme.Modules.restrictUnitIso U.ι
  letI : IsIso qU := affineSource_unit_isIso_of_isIso (f ∣_ U)
  letI : IsIso ePush.hom := ePush.isIso_hom
  letI : IsIso eUnit.hom := eUnit.isIso_hom
  letI : IsIso (F.map q ≫ ePush.hom) := by
    rw [openRestrictPushforwardUnitIso_unit f U]
    change IsIso (eUnit.hom ≫ qU)
    infer_instance
  letI : IsIso (F.map q) := IsIso.of_isIso_comp_right (F.map q) ePush.hom
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  have hzero : IsZero (F.obj (cokernel q)) :=
    (isZero_cokernel_of_epi (F.map q)).of_iso (PreservesCokernel.iso F q)
  intro x hx hxU
  let y : U.toScheme.carrier := ⟨x, hxU⟩
  have hy : y ∈ schemeModuleStalkSupport (F.obj (cokernel q)) := by
    rw [schemeModuleStalkSupport_restrict]
    exact hx
  let G := schemeModuleStalkModuleFunctor U.toScheme y
  letI : G.Additive := inferInstanceAs ((schemeModuleStalkModuleFunctor U.toScheme y).Additive)
  letI : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive G
  have hsub : Subsingleton ((F.obj (cokernel q)).presheaf.stalk y) :=
    ModuleCat.subsingleton_of_isZero (Functor.map_isZero G hzero)
  exact (not_nontrivial_iff_subsingleton.mpr hsub) hy

end PfaffianDescent.Coray

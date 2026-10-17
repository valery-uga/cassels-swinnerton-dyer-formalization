import PfaffianDescent.SheafModuleFlasque

/-!
# Global sections of a pushed-forward structure sheaf

The affine coordinate algebra of a finite subscheme is the global-section
space of its structure sheaf after pushforward to the ambient scheme.  This
is the untwisted target-side comparison used in Voisin's restriction map.
-/

noncomputable section

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

/-- An isomorphism of module sheaves induces an equivalence of their global
section spaces. -/
noncomputable def schemeModuleSectionsEquivOfIso
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    M.sections ≃ N.sections where
  toFun := SheafOfModules.sectionsMap e.hom
  invFun := SheafOfModules.sectionsMap e.inv
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    change ((e.hom ≫ e.inv).app U.unop) (s.val U) = s.val U
    rw [e.hom_inv_id]
    rfl
  right_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    change ((e.inv ≫ e.hom).app U.unop) (s.val U) = s.val U
    rw [e.inv_hom_id]
    rfl

/-- Global sections commute with direct image along a scheme morphism.  At
the top open, the pushed-forward module presheaf is definitionally the
original module presheaf at the top open of the source. -/
noncomputable def pushforwardModuleSectionsEquiv
    {X Z : Scheme.{u}} (i : Z ⟶ X) (M : Z.Modules) :
    ((Scheme.Modules.pushforward i).obj M).sections ≃ M.sections := by
  let N := (Scheme.Modules.pushforward i).obj M
  exact (moduleSectionsEquivTop X N).trans
    { toFun := fun x ↦ (moduleSectionsEquivTop Z M).symm x
      invFun := fun x ↦ moduleSectionsEquivTop Z M x
      left_inv := fun x ↦ (moduleSectionsEquivTop Z M).apply_symm_apply x
      right_inv := fun x ↦ (moduleSectionsEquivTop Z M).symm_apply_apply x }

/-- Global sections of the pushforward of `O_Z` are canonically the ordinary
global functions on `Z`.  No finiteness hypothesis is needed for this
categorical identification. -/
noncomputable def pushforwardUnitSectionsEquiv
    {X Z : Scheme.{u}} (i : Z ⟶ X) :
    ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)).sections ≃ Γ(Z, ⊤) := by
  let M := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  exact (pushforwardModuleSectionsEquiv i
    (SheafOfModules.unit Z.ringCatSheaf)).trans
    (moduleSectionsEquivTop Z (SheafOfModules.unit Z.ringCatSheaf))

/-- The target of the unit-twisted closed-immersion ideal sequence is the
ordinary pushed-forward structure sheaf of the closed subscheme. -/
noncomputable def closedImmersionIdealTwistSequenceUnitTargetIso
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf) :=
  schemeModuleTensorUnitRightIso
    ((IdealSheafDataModule.closedImmersionModulePushforwardSequence i).X₃)

/-- In the unit-twist case, the target section space in the ideal sequence is
canonically the coordinate algebra of the closed subscheme. -/
noncomputable def closedImmersionIdealTwistSequenceUnitTargetSectionsEquiv
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃.sections ≃ Γ(Z, ⊤) :=
  (schemeModuleSectionsEquivOfIso
    (closedImmersionIdealTwistSequenceUnitTargetIso i)).trans
      (pushforwardUnitSectionsEquiv i)

/-- If a twist is trivialized, the target of the corresponding twisted ideal
sequence is the ordinary pushed-forward structure sheaf.  This is designed
to be applied on an affine chart where a projective twist is trivial. -/
noncomputable def closedImmersionIdealTwistSequenceTargetIsoOfIsoUnit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {L : X.Modules} (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    (closedImmersionIdealTwistSequence i L).X₃ ≅
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf) :=
  ((schemeModuleTensorRightCongr e).app
    ((IdealSheafDataModule.closedImmersionModulePushforwardSequence i).X₃)) ≪≫
      schemeModuleTensorUnitRightIso
        ((IdealSheafDataModule.closedImmersionModulePushforwardSequence i).X₃)

/-- Under a chosen trivialization of the twist, target sections in the
twisted ideal sequence are the coordinate algebra of the closed subscheme. -/
noncomputable def closedImmersionIdealTwistSequenceTargetSectionsEquivOfIsoUnit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {L : X.Modules} (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    (closedImmersionIdealTwistSequence i L).X₃.sections ≃ Γ(Z, ⊤) :=
  (schemeModuleSectionsEquivOfIso
    (closedImmersionIdealTwistSequenceTargetIsoOfIsoUnit i e)).trans
      (pushforwardUnitSectionsEquiv i)

end PfaffianDescent

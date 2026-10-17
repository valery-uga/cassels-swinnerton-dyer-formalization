import PfaffianDescent.FieldPointUnitQuotientMaximalIdeal

/-! # Stalk Ext equivalence from a constructed point residue presentation

The retained presentation and its proved parameter ideal determine a bijective
local coordinate. The constructed global residue equivalence then proves that
the actual global-to-stalk Ext map is bijective, without another locality premise.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The actual free stalk coordinates and regular parameters give a residue
field coordinate for the stalk Ext group. -/
def fieldPointStalkResidueAddEquivOfPresentation
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (Y : X.Modules)
    (e : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2 ≃+ L)
    (d : FieldPointExtResiduePresentation i x
      (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ Y e) :
    Ext.{u + 1}
      ((schemeModuleStalkModuleFunctor X (i x)).obj
        (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃)
      ((schemeModuleStalkModuleFunctor X (i x)).obj Y) 2 ≃+ L :=
  ((extPostcompIsoOfIso d.qN).trans (extPrecompIsoOfIso d.qM)).trans
    ((localExtTwoResidueCoordinateAddEquiv d.f d.g d.hf d.hg d.hfm d.hgm
      (d.span_eq_maximalIdeal_of_unit_source i x Y e)).trans
      (closedFieldPointResidueRingEquivAt i x).toAddEquiv)

set_option backward.isDefEq.respectTransparency false in
/-- The stalk residue coordinate recovers the already constructed global
coordinate after the actual stalk Ext map. -/
theorem fieldPointStalkResidueAddEquivOfPresentation_stalkMap
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (Y : X.Modules)
    (e : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2 ≃+ L)
    (d : FieldPointExtResiduePresentation i x
      (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ Y e)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2) :
    fieldPointStalkResidueAddEquivOfPresentation i x Y e d
      (schemeModuleStalkModuleExtMap X (i x)
        (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2 z) =
      e z := by
  rw [d.coordinate_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A constructed field-valued residue equivalence proves actual stalk
locality for its unit-twisted closed-point Ext group. -/
theorem fieldPointStalkExtMap_bijective_of_residuePresentation
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (Y : X.Modules)
    (e : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2 ≃+ L)
    (d : FieldPointExtResiduePresentation i x
      (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ Y e) :
    Function.Bijective (schemeModuleStalkModuleExtMap X (i x)
      (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2) := by
  let t := fieldPointStalkResidueAddEquivOfPresentation i x Y e d
  constructor
  · intro z w hzw
    apply e.injective
    rw [← fieldPointStalkResidueAddEquivOfPresentation_stalkMap i x Y e d z,
      ← fieldPointStalkResidueAddEquivOfPresentation_stalkMap i x Y e d w]
    exact congrArg t hzw
  · intro a
    refine ⟨e.symm (t a), ?_⟩
    apply t.injective
    exact (fieldPointStalkResidueAddEquivOfPresentation_stalkMap i x Y e d _).trans
      (e.apply_symm_apply (t a))

end PfaffianDescent

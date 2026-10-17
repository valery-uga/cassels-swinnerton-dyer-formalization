import PfaffianDescent.FieldPointExtResiduePresentation

/-! # The actual residue-field action on constructed point Ext coordinates

The scalar action is precomposition by multiplication on the actual point
pushforward. Its compatibility with a retained residue coordinate is proved,
rather than imposed when defining a vector-space structure.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Actual point multiplication by a residue-field scalar multiplies every
constructed unit-source Ext coordinate by that scalar. -/
theorem fieldPointResiduePresentation_precomp_unit_scalar
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (Y : X.Modules)
    (e : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2 ≃+ L)
    (d : FieldPointExtResiduePresentation i x
      (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ Y e)
    (a : L) (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2) :
    e ((Ext.mk₀.{u} (C := X.Modules)
      (fieldPointPushforwardTwistScalarEndomorphismAddHom i
        (SheafOfModules.unit X.ringCatSheaf) a)).comp z (zero_add 2)) = a * e z := by
  rw [d.coordinate_eq, d.coordinate_eq]
  exact fieldPointExtTwoResidueCoordinate_precomp_twistScalar i
    (SheafOfModules.unit X.ringCatSheaf) (Iso.refl _) x Y
    d.f d.g d.hf d.hg d.hfm d.hgm d.qM d.qN a z

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition by actual point multiplication realizes every scalar
multiple in the constructed coordinate, as an equality of actual Ext classes. -/
theorem fieldPointResiduePresentation_precomp_unit_scalar_eq_symm
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (Y : X.Modules)
    (e : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2 ≃+ L)
    (d : FieldPointExtResiduePresentation i x
      (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃ Y e)
    (a : L) (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit X.ringCatSheaf)).X₃ Y 2) :
    (Ext.mk₀.{u} (C := X.Modules)
      (fieldPointPushforwardTwistScalarEndomorphismAddHom i
        (SheafOfModules.unit X.ringCatSheaf) a)).comp z (zero_add 2) =
      e.symm (a * e z) := by
  apply e.injective
  rw [e.apply_symm_apply]
  exact fieldPointResiduePresentation_precomp_unit_scalar i x Y e d a z

end PfaffianDescent

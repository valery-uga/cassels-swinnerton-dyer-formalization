import PfaffianDescent.SchemeCoverRefinementExt
import PfaffianDescent.SectionRepresenterTop
import PfaffianDescent.SchemeModuleCohomology

/-!
# Intrinsic degree-two cohomology from covering cocycles

Canonical augmentation-target identifications turn the covering Ext class
into intrinsic scheme-module cohomology. Refinement gives exactly the same
intrinsic class, so covers can be compared through common refinements.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PfaffianDescent

universe u

variable {X : Scheme.{u}} {ι : Type u}

/-- The canonical formal Cech augmentation target is the structure sheaf. -/
def schemeCoverCechTargetIsoUnit (U : ι → X.Opens) :
    (sectionRepresenterCechAugmented X.ringCatSheaf U ⊤ isTerminalTop).right ≅
      SheafOfModules.unit X.ringCatSheaf :=
  sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf U ⊤ isTerminalTop ≪≫
    sectionRepresenterTopIsoUnit X

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic degree-two cohomology class of an actual covering cocycle. -/
def schemeCoverDegreeTwoToCohomology (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) [HasExt.{u} X.Modules]
    (Y : X.Modules)
    (z : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 3 2) (Y := Y)) :
    schemeModuleCohomology X Y 2 :=
  (Ext.mk₀ (C := X.Modules) (schemeCoverCechTargetIsoUnit U).inv).comp
    (schemeCoverDegreeTwoToExt U hU Y z) (zero_add 2)

set_option backward.isDefEq.respectTransparency false in
/-- Refinement preserves the actual intrinsic cohomology class, with no
remaining source transport or comparison equality supplied as a premise. -/
theorem schemeCoverDegreeTwoToCohomology_refinement
    {κ : Type u} (U : ι → X.Opens) (W : κ → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (hW : (Opens.grothendieckTopology X).CoversTop W)
    (σ : κ → ι) (j : ∀ k, W k ⟶ U (σ k))
    [hExt : HasExt.{u} X.Modules] (Y : X.Modules)
    (z : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 3 2) (Y := Y)) :
    schemeCoverDegreeTwoToCohomology U hU Y z =
      schemeCoverDegreeTwoToCohomology W hW Y
        (DegreeTwoCocycle.precompAddHom _ _
          ((sectionRepresenterCechRefinement X.ringCatSheaf U W σ j).f 2)
          ((sectionRepresenterCechRefinement X.ringCatSheaf U W σ j).f 3)
          ((sectionRepresenterCechRefinement X.ringCatSheaf U W σ j).comm 3 2).symm z) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  have h := congrArg (fun t ↦
    (Ext.mk₀ (C := X.Modules) (schemeCoverCechTargetIsoUnit W).inv).comp t (zero_add 2))
      (schemeCoverDegreeTwoToExt_refinement U W hU hW σ j Y z)
  rw [Ext.mk₀_comp_mk₀_assoc] at h
  have hc : (schemeCoverCechTargetIsoUnit W).inv ≫
      ((sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf W ⊤ isTerminalTop).hom ≫
        (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf U ⊤ isTerminalTop).inv) =
      (schemeCoverCechTargetIsoUnit U).inv := by
    simp only [schemeCoverCechTargetIsoUnit, Iso.trans_inv, Category.assoc,
      Iso.inv_hom_id_assoc]
  rw [hc] at h
  exact h

end PfaffianDescent

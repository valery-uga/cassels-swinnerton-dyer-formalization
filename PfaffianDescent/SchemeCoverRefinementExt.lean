import PfaffianDescent.SectionRepresenterCechRefinement
import PfaffianDescent.SectionRepresenterCechAugmentationExact
import PfaffianDescent.SectionRepresenterCechLocalExact
import PfaffianDescent.AugmentedChainSourceNaturality

/-!
# Refinement invariance of actual covering Cech Ext classes

The cover hypotheses discharge exactness and epimorphy. Refinement maps
therefore compare actual degree-two Ext classes, without assuming any
comparison squares or exactness data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PfaffianDescent

universe u

variable {X : Scheme.{u}} {ι : Type u}

theorem schemeCoverCech_exact_one (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) :
    (ShortComplex.mk ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      ((sectionRepresenterCechChain X.ringCatSheaf U).d 1 0)
      ((sectionRepresenterCechChain X.ringCatSheaf U).d_comp_d 2 1 0)).Exact := by
  have h := sectionRepresenterCechChain_exactAt_succ_of_coversTop X.ringCatSheaf U hU 0
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at h
  exact h

theorem schemeCoverCech_exact_two (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) :
    (ShortComplex.mk ((sectionRepresenterCechChain X.ringCatSheaf U).d 3 2)
      ((sectionRepresenterCechChain X.ringCatSheaf U).d 2 1)
      ((sectionRepresenterCechChain X.ringCatSheaf U).d_comp_d 3 2 1)).Exact := by
  have h := sectionRepresenterCechChain_exactAt_succ_of_coversTop X.ringCatSheaf U hU 1
  rw [HomologicalComplex.exactAt_iff' _ 3 2 1 (by simp) (by simp)] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The actual class of a cocycle on an arbitrary covering family of opens. -/
def schemeCoverDegreeTwoToExt (U : ι → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U) [hExt : HasExt.{u} X.Modules]
    (Y : X.Modules)
    (z : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 3 2) (Y := Y)) :
    Ext (C := X.Modules)
      (sectionRepresenterCechAugmented X.ringCatSheaf U ⊤ isTerminalTop).right Y 2 := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let C : ChainComplex X.Modules ℕ := sectionRepresenterCechChain X.ringCatSheaf U
  let P : X.Modules := (sectionRepresenterCechAugmented X.ringCatSheaf U ⊤ isTerminalTop).right
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop
  let hex := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf U hU ⊤ isTerminalTop
  letI : Epi eps := hex.2
  exact augmentedChainDegreeTwoToExt P (C.X 0) (C.X 1) (C.X 2) (C.X 3) Y
    eps (C.d 1 0) (C.d 2 1) (C.d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf U ⊤ isTerminalTop)
    (C.d_comp_d 2 1 0) (C.d_comp_d 3 2 1)
    hex.1 (schemeCoverCech_exact_one U hU) (schemeCoverCech_exact_two U hU) z

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a cocycle to a refined covering family preserves its actual
Ext class after the canonical formal-augmentation-target identification. -/
theorem schemeCoverDegreeTwoToExt_refinement
    {κ : Type u} (U : ι → X.Opens) (W : κ → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    (hW : (Opens.grothendieckTopology X).CoversTop W)
    (σ : κ → ι) (j : ∀ k, W k ⟶ U (σ k))
    [hExt : HasExt.{u} X.Modules] (Y : X.Modules)
    (z : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf U).d 3 2) (Y := Y)) :
    (Ext.mk₀ (C := X.Modules)
      ((sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf W ⊤ isTerminalTop).hom ≫
        (sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf U ⊤ isTerminalTop).inv)).comp
      (schemeCoverDegreeTwoToExt U hU Y z) (zero_add 2) =
    schemeCoverDegreeTwoToExt W hW Y
      (DegreeTwoCocycle.precompAddHom _ _
        ((sectionRepresenterCechRefinement X.ringCatSheaf U W σ j).f 2)
        ((sectionRepresenterCechRefinement X.ringCatSheaf U W σ j).f 3)
        ((sectionRepresenterCechRefinement X.ringCatSheaf U W σ j).comm 3 2).symm z) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let C := sectionRepresenterCechChain X.ringCatSheaf W
  let D := sectionRepresenterCechChain X.ringCatSheaf U
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf W ⊤ isTerminalTop
  let eta := sectionRepresenterCechAugmentation X.ringCatSheaf U ⊤ isTerminalTop
  let eW := sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf W ⊤ isTerminalTop
  let eU := sectionRepresenterCechTargetIsoTerminal X.ringCatSheaf U ⊤ isTerminalTop
  let a := sectionRepresenterCechRefinement X.ringCatSheaf U W σ j
  let hw := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf W hW ⊤ isTerminalTop
  let hu := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf U hU ⊤ isTerminalTop
  letI : Epi eps := hw.2
  letI : Epi eta := hu.2
  have haug : eps ≫ (eW.hom ≫ eU.inv) = a.f 0 ≫ eta := by
    have h := congrArg (fun k ↦ k ≫ eU.inv)
      (sectionRepresenterCechRefinement_augmentation X.ringCatSheaf U W σ j ⊤ isTerminalTop)
    change (a.f 0 ≫ eta ≫ eU.hom) ≫ eU.inv = (eps ≫ eW.hom) ≫ eU.inv at h
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm
  exact augmentedChainDegreeTwoToExt_precomp
    _ (C.X 0) (C.X 1) (C.X 2) (C.X 3)
    _ (D.X 0) (D.X 1) (D.X 2) (D.X 3) Y
    eps (C.d 1 0) (C.d 2 1) (C.d 3 2)
    eta (D.d 1 0) (D.d 2 1) (D.d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf W ⊤ isTerminalTop)
    (C.d_comp_d 2 1 0) (C.d_comp_d 3 2 1)
    (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf U ⊤ isTerminalTop)
    (D.d_comp_d 2 1 0) (D.d_comp_d 3 2 1)
    hw.1 (schemeCoverCech_exact_one W hW) (schemeCoverCech_exact_two W hW)
    hu.1 (schemeCoverCech_exact_one U hU) (schemeCoverCech_exact_two U hU)
    (eW.hom ≫ eU.inv) (a.f 0) (a.f 1) (a.f 2) (a.f 3)
    haug (a.comm 1 0).symm (a.comm 2 1).symm (a.comm 3 2).symm z

end PfaffianDescent

import PfaffianDescent.SectionRepresenterKoszulExt
import PfaffianDescent.DegreeTwoResolutionNaturality

/-!
# Coefficient naturality of the point Koszul class

Applying a module morphism to a coefficient section gives precisely
postcomposition of its global Yoneda class. This supplies the coefficient
multiplication step in comparing point residues with Cech duality.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped ZeroObject
namespace PfaffianDescent
universe u
variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasExt.{u} (SheafOfModules.{u} R)]
local notation "P⟦" U "⟧" => sectionRepresenter R U
set_option backward.isDefEq.respectTransparency false in
/-- Coefficient morphisms commute with the point Koszul Yoneda class. -/
theorem sectionRepresenterKoszulDegreeTwoClass_postcomp
    (U : C) (q f : R.val.obj (op U)) (hcomm : Commute q f)
    (M Y Z : SheafOfModules.{u} R) (m : M.val.obj (op U))
    (hq : q • m = 0) (hf : f • m = 0)
    (hexact₀ : (ShortComplex.mk
      (sectionRepresenterKoszulLast R U q f)
      (sectionRepresenterKoszulAugmentation R U M m)
      (sectionRepresenterKoszulLast_comp_augmentation
        R U q f M m hq hf)).Exact)
    (hexact₁ : (ShortComplex.mk
      (sectionRepresenterKoszulFirst R U q f)
      (sectionRepresenterKoszulLast R U q f)
      (sectionRepresenterKoszul_comp_zero R U q f hcomm)).Exact)
    (hexact₂ : (ShortComplex.mk
      (0 : (0 : SheafOfModules.{u} R) ⟶ P⟦U⟧)
      (sectionRepresenterKoszulFirst R U q f) zero_comp).Exact)
    [Epi (sectionRepresenterKoszulAugmentation R U M m)] (y : Y.val.obj (op U)) (h : Y ⟶ Z) :
    (sectionRepresenterKoszulDegreeTwoClass R U q f hcomm
      M Y m hq hf hexact₀ hexact₁ hexact₂ y).comp (Ext.mk₀ h) (add_zero 2) =
    sectionRepresenterKoszulDegreeTwoClass R U q f hcomm
      M Z m hq hf hexact₀ hexact₁ hexact₂ (h.val.app (op U) y) := by
  unfold sectionRepresenterKoszulDegreeTwoClass
  rw [augmentedChainDegreeTwoToExt_postcomp]
  congr 1
  apply Subtype.ext
  apply (sectionRepresenterHomEquiv R U Z).injective
  change (sectionRepresenterHomEquiv R U Z)
    (sectionRepresenterAugmentation R U Y y ≫ h) =
      (sectionRepresenterHomEquiv R U Z)
        (sectionRepresenterAugmentation R U Z (h.val.app (op U) y))
  rw [sectionRepresenterHomEquiv_postcomp]
  simp only [sectionRepresenterAugmentation, Equiv.apply_symm_apply]

end PfaffianDescent

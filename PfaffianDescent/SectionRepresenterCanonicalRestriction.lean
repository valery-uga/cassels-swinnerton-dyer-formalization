import PfaffianDescent.SectionRepresenterTop
import PfaffianDescent.CanonicalPointRestriction

/-!
# Canonical restriction as a section-representer augmentation

The augmentation represented by the image of one is the original morphism
from the structure sheaf, after the canonical top-representer identification.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterTopIsoUnit_hom_coordinate (X : Scheme.{u}) :
    sectionRepresenterHomEquiv X.ringCatSheaf (⊤ : X.Opens)
      (SheafOfModules.unit X.ringCatSheaf) (sectionRepresenterTopIsoUnit X).hom =
        (1 : Γ(X, ⊤)) := by
  change sectionRepresenterHomEquiv X.ringCatSheaf (⊤ : X.Opens)
    (SheafOfModules.unit X.ringCatSheaf)
    ((sectionRepresenterHomEquiv X.ringCatSheaf (⊤ : X.Opens)
      (SheafOfModules.unit X.ringCatSheaf)).symm
        (moduleSectionsEquivTop X (SheafOfModules.unit X.ringCatSheaf)
          ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (𝟙 _)))) = (1 : Γ(X, ⊤))
  rw [Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sectionRepresenterAugmentation_top_image_one
    {X : Scheme.{u}} {M : X.Modules}
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    sectionRepresenterAugmentation X.ringCatSheaf ⊤ M
      (φ.val.app (op ⊤) (1 : Γ(X, ⊤))) =
      (sectionRepresenterTopIsoUnit X).hom ≫ φ := by
  apply (sectionRepresenterHomEquiv X.ringCatSheaf (⊤ : X.Opens) M).injective
  rw [sectionRepresenterHomEquiv_augmentation, sectionRepresenterHomEquiv_postcomp,
    sectionRepresenterTopIsoUnit_hom_coordinate]

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation of the actual closed-subscheme restriction of one is
the actual restriction morphism, with the canonical source and target isos. -/
theorem sectionRepresenterAugmentation_top_canonicalRestriction
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    sectionRepresenterAugmentation X.ringCatSheaf ⊤
        (closedImmersionIdealTwistSequence i (SheafOfModules.unit X.ringCatSheaf)).X₃
        (closedImmersionUnitTwistRestrictionSection i ⊤ 1) =
      (sectionRepresenterTopIsoUnit X).hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
          (closedImmersionIdealTwistSequenceUnitTargetIso i).inv := by
  exact sectionRepresenterAugmentation_top_image_one
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
      (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)

end PfaffianDescent

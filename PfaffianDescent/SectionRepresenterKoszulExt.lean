import PfaffianDescent.SectionRepresenterKoszul
import PfaffianDescent.CechExtDegreeTwo

/-!
# Degree-two Ext from the section-representer Koszul resolution

This file packages the noncircular point-class construction.  Once the
augmented two-generator Koszul complex is exact, sections on the affine open
give global degree-two Ext classes.  The boundary calculation is literal:
the kernel consists of `(-f) • a + q • b`.
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

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

local notation "P⟦" U "⟧" => sectionRepresenter R U

/-- The two middle Koszul summands are Ext-acyclic whenever the single
section representer is Ext-acyclic in that degree. -/
theorem sectionRepresenterKoszulPair_ext_subsingleton
    (U : C) (Y : SheafOfModules.{u} R) (n : ℕ)
    [Subsingleton (Ext P⟦U⟧ Y n)] :
    Subsingleton (Ext (⨁ sectionRepresenterKoszulPair R U) Y n) := by
  letI : ∀ j : Fin 2, Subsingleton
      (Ext (sectionRepresenterKoszulPair R U j) Y n) := fun _ ↦ inferInstance
  exact (Equiv.subsingleton_congr
    (Ext.biproductAddEquiv
      (biproduct.isBilimit (sectionRepresenterKoszulPair R U)) Y n).toEquiv).mpr
    inferInstance

/-- A section of the coefficient sheaf is a degree-two cocycle for the
Koszul resolution, whose preceding term is zero. -/
noncomputable def sectionRepresenterKoszulDegreeTwoCocycle
    (U : C) (Y : SheafOfModules.{u} R) (y : Y.val.obj (op U)) :
    DegreeTwoCocycle
      (0 : (0 : SheafOfModules.{u} R) ⟶ P⟦U⟧) (Y := Y) :=
  ⟨sectionRepresenterAugmentation R U Y y, by
    change (0 : (0 : SheafOfModules.{u} R) ⟶ P⟦U⟧) ≫
      sectionRepresenterAugmentation R U Y y = 0
    rw [zero_comp]⟩

@[simp]
theorem sectionRepresenterKoszulDegreeTwoCocycle_zero
    (U : C) (Y : SheafOfModules.{u} R) :
    sectionRepresenterKoszulDegreeTwoCocycle R U Y 0 = 0 := by
  apply Subtype.ext
  exact sectionRepresenterAugmentation_zero R U Y

theorem sectionRepresenterKoszulDegreeTwoCocycle_add
    (U : C) (Y : SheafOfModules.{u} R) (y z : Y.val.obj (op U)) :
    sectionRepresenterKoszulDegreeTwoCocycle R U Y (y + z) =
      sectionRepresenterKoszulDegreeTwoCocycle R U Y y +
        sectionRepresenterKoszulDegreeTwoCocycle R U Y z := by
  apply Subtype.ext
  exact sectionRepresenterAugmentation_add R U Y y z

/-- The global `Ext²` class represented by a section in an exact augmented
section-representer Koszul resolution. -/
noncomputable def sectionRepresenterKoszulDegreeTwoClass
    (U : C) (q f : R.val.obj (op U)) (hcomm : Commute q f)
    (M Y : SheafOfModules.{u} R) (m : M.val.obj (op U))
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
    [Epi (sectionRepresenterKoszulAugmentation R U M m)]
    (y : Y.val.obj (op U)) : Ext M Y 2 :=
  augmentedChainDegreeTwoToExt
    M P⟦U⟧ (⨁ sectionRepresenterKoszulPair R U) P⟦U⟧
      (0 : SheafOfModules.{u} R) Y
    (sectionRepresenterKoszulAugmentation R U M m)
    (sectionRepresenterKoszulLast R U q f)
    (sectionRepresenterKoszulFirst R U q f)
    (0 : (0 : SheafOfModules.{u} R) ⟶ P⟦U⟧)
    (sectionRepresenterKoszulLast_comp_augmentation R U q f M m hq hf)
    (sectionRepresenterKoszul_comp_zero R U q f hcomm)
    zero_comp hexact₀ hexact₁ hexact₂
    (sectionRepresenterKoszulDegreeTwoCocycle R U Y y)

@[simp]
theorem sectionRepresenterKoszulDegreeTwoClass_zero
    (U : C) (q f : R.val.obj (op U)) (hcomm : Commute q f)
    (M Y : SheafOfModules.{u} R) (m : M.val.obj (op U))
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
    [Epi (sectionRepresenterKoszulAugmentation R U M m)] :
    sectionRepresenterKoszulDegreeTwoClass R U q f hcomm
      M Y m hq hf hexact₀ hexact₁ hexact₂ 0 = 0 := by
  unfold sectionRepresenterKoszulDegreeTwoClass
  rw [sectionRepresenterKoszulDegreeTwoCocycle_zero,
    augmentedChainDegreeTwoToExt_zero]

theorem sectionRepresenterKoszulDegreeTwoClass_add
    (U : C) (q f : R.val.obj (op U)) (hcomm : Commute q f)
    (M Y : SheafOfModules.{u} R) (m : M.val.obj (op U))
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
    [Epi (sectionRepresenterKoszulAugmentation R U M m)]
    (y z : Y.val.obj (op U)) :
    sectionRepresenterKoszulDegreeTwoClass R U q f hcomm
        M Y m hq hf hexact₀ hexact₁ hexact₂ (y + z) =
      sectionRepresenterKoszulDegreeTwoClass R U q f hcomm
          M Y m hq hf hexact₀ hexact₁ hexact₂ y +
        sectionRepresenterKoszulDegreeTwoClass R U q f hcomm
          M Y m hq hf hexact₀ hexact₁ hexact₂ z := by
  unfold sectionRepresenterKoszulDegreeTwoClass
  rw [sectionRepresenterKoszulDegreeTwoCocycle_add,
    augmentedChainDegreeTwoToExt_add]

/-- The explicit Koszul construction as an additive homomorphism from affine
sections to global degree-two Ext. -/
noncomputable def sectionRepresenterKoszulDegreeTwoClassAddHom
    (U : C) (q f : R.val.obj (op U)) (hcomm : Commute q f)
    (M Y : SheafOfModules.{u} R) (m : M.val.obj (op U))
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
    [Epi (sectionRepresenterKoszulAugmentation R U M m)] :
    Y.val.obj (op U) →+ Ext M Y 2 where
  toFun := sectionRepresenterKoszulDegreeTwoClass R U q f hcomm
    M Y m hq hf hexact₀ hexact₁ hexact₂
  map_zero' := sectionRepresenterKoszulDegreeTwoClass_zero R U q f hcomm
    M Y m hq hf hexact₀ hexact₁ hexact₂
  map_add' := sectionRepresenterKoszulDegreeTwoClass_add R U q f hcomm
    M Y m hq hf hexact₀ hexact₁ hexact₂

/-- Affine sections generate all global degree-two classes once the first two
section-representer terms are Ext-acyclic. -/
theorem sectionRepresenterKoszulDegreeTwoClass_surjective
    (U : C) (q f : R.val.obj (op U)) (hcomm : Commute q f)
    (M Y : SheafOfModules.{u} R) (m : M.val.obj (op U))
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
    [Epi (sectionRepresenterKoszulAugmentation R U M m)]
    [Subsingleton (Ext P⟦U⟧ Y 2)]
    [Subsingleton (Ext (⨁ sectionRepresenterKoszulPair R U) Y 1)] :
    Function.Surjective
      (sectionRepresenterKoszulDegreeTwoClass R U q f hcomm
        M Y m hq hf hexact₀ hexact₁ hexact₂) := by
  intro z
  obtain ⟨c, hc⟩ := augmentedChainDegreeTwoToExt_surjective
    M P⟦U⟧ (⨁ sectionRepresenterKoszulPair R U) P⟦U⟧
      (0 : SheafOfModules.{u} R) Y
    (sectionRepresenterKoszulAugmentation R U M m)
    (sectionRepresenterKoszulLast R U q f)
    (sectionRepresenterKoszulFirst R U q f)
    (0 : (0 : SheafOfModules.{u} R) ⟶ P⟦U⟧)
    (sectionRepresenterKoszulLast_comp_augmentation R U q f M m hq hf)
    (sectionRepresenterKoszul_comp_zero R U q f hcomm)
    zero_comp hexact₀ hexact₁ hexact₂ z
  let y := sectionRepresenterHomEquiv R U Y c.1
  refine ⟨y, ?_⟩
  unfold sectionRepresenterKoszulDegreeTwoClass
  rw [show sectionRepresenterKoszulDegreeTwoCocycle R U Y y = c by
    apply Subtype.ext
    exact (Equiv.symm_apply_apply (sectionRepresenterHomEquiv R U Y) c.1)]
  exact hc

/-- The explicit degree-two class vanishes exactly on the two-generator
Koszul boundary. -/
theorem sectionRepresenterKoszulDegreeTwoClass_eq_zero_iff
    (U : C) (q f : R.val.obj (op U)) (hcomm : Commute q f)
    (M Y : SheafOfModules.{u} R) (m : M.val.obj (op U))
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
    [Epi (sectionRepresenterKoszulAugmentation R U M m)]
    [Subsingleton (Ext P⟦U⟧ Y 1)]
    (y : Y.val.obj (op U)) :
    sectionRepresenterKoszulDegreeTwoClass R U q f hcomm
        M Y m hq hf hexact₀ hexact₁ hexact₂ y = 0 ↔
      ∃ a b : Y.val.obj (op U), (-f) • a + q • b = y := by
  unfold sectionRepresenterKoszulDegreeTwoClass
  rw [augmentedChainDegreeTwoToExt_eq_zero_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨sectionRepresenterHomAddEquiv R U Y
        (biproduct.ι (sectionRepresenterKoszulPair R U) 0 ≫ g),
      sectionRepresenterHomAddEquiv R U Y
        (biproduct.ι (sectionRepresenterKoszulPair R U) 1 ≫ g), ?_⟩
    rw [← sectionRepresenterKoszulFirst_hom_coordinate R U q f Y g, hg]
    change sectionRepresenterHomAddEquiv R U Y
      (sectionRepresenterAugmentation R U Y y) = y
    exact sectionRepresenterHomAddEquiv_augmentation R U Y y
  · rintro ⟨a, b, hab⟩
    let g : (⨁ sectionRepresenterKoszulPair R U) ⟶ Y :=
      biproduct.desc
        ![sectionRepresenterAugmentation R U Y a,
          sectionRepresenterAugmentation R U Y b]
    refine ⟨g, ?_⟩
    apply (sectionRepresenterHomAddEquiv R U Y).injective
    rw [sectionRepresenterKoszulFirst_hom_coordinate]
    simpa only [g, sectionRepresenterKoszulDegreeTwoCocycle,
      biproduct.ι_desc, Matrix.cons_val_zero, Matrix.cons_val_one,
      sectionRepresenterHomAddEquiv_augmentation] using hab

/-- A section outside the explicit two-generator Koszul boundary represents
a nonzero global degree-two class. -/
theorem sectionRepresenterKoszulDegreeTwoClass_ne_zero
    (U : C) (q f : R.val.obj (op U)) (hcomm : Commute q f)
    (M Y : SheafOfModules.{u} R) (m : M.val.obj (op U))
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
    [Epi (sectionRepresenterKoszulAugmentation R U M m)]
    [Subsingleton (Ext P⟦U⟧ Y 1)]
    (y : Y.val.obj (op U))
    (hy : ¬ ∃ a b : Y.val.obj (op U), (-f) • a + q • b = y) :
    sectionRepresenterKoszulDegreeTwoClass R U q f hcomm
      M Y m hq hf hexact₀ hexact₁ hexact₂ y ≠ 0 := by
  intro hzero
  exact hy ((sectionRepresenterKoszulDegreeTwoClass_eq_zero_iff
    R U q f hcomm M Y m hq hf hexact₀ hexact₁ hexact₂ y).mp hzero)

end PfaffianDescent

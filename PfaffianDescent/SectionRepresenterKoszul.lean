import PfaffianDescent.SectionRepresenterScalar
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The two-generator Koszul complex on a section representer

For two functions on an open, this file builds the global sheaf maps whose
restriction to that open is the usual Koszul complex.  It is the source
resolution used to compute the degree-two Ext class of a closed point.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace PfaffianDescent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "P⟦" U "⟧" => sectionRepresenter R U

/-- The two identical middle summands of the Koszul complex. -/
abbrev sectionRepresenterKoszulPair (U : C) : Fin 2 → SheafOfModules.{u} R :=
  fun _ ↦ P⟦U⟧

/-- The first Koszul differential `a ↦ (-f a, q a)`. -/
noncomputable def sectionRepresenterKoszulFirst
    (U : C) (q f : R.val.obj (op U)) :
    P⟦U⟧ ⟶ ⨁ sectionRepresenterKoszulPair R U :=
  biproduct.lift
    ![sectionRepresenterScalarEndomorphism R U (-f),
      sectionRepresenterScalarEndomorphism R U q]

/-- The last Koszul differential `(a,b) ↦ q a + f b`. -/
noncomputable def sectionRepresenterKoszulLast
    (U : C) (q f : R.val.obj (op U)) :
    (⨁ sectionRepresenterKoszulPair R U) ⟶ P⟦U⟧ :=
  biproduct.desc
    ![sectionRepresenterScalarEndomorphism R U q,
      sectionRepresenterScalarEndomorphism R U f]

/-- The two Koszul differentials compose to zero. -/
theorem sectionRepresenterKoszul_comp_zero
    (U : C) (q f : R.val.obj (op U)) (hcomm : Commute q f) :
    sectionRepresenterKoszulFirst R U q f ≫
      sectionRepresenterKoszulLast R U q f = 0 := by
  rw [sectionRepresenterKoszulFirst, sectionRepresenterKoszulLast,
    biproduct.lift_desc]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [sectionRepresenterScalarEndomorphism_comp,
    sectionRepresenterScalarEndomorphism_comp,
    ← sectionRepresenterScalarEndomorphism_add]
  convert sectionRepresenterScalarEndomorphism_zero R U using 2
  rw [neg_mul, hcomm.eq, neg_add_cancel]

/-- The section-representer Koszul short complex. -/
noncomputable def sectionRepresenterKoszulShortComplex
    (U : C) (q f : R.val.obj (op U)) (hcomm : Commute q f) :
    ShortComplex (SheafOfModules.{u} R) :=
  ShortComplex.mk
    (sectionRepresenterKoszulFirst R U q f)
    (sectionRepresenterKoszulLast R U q f)
    (sectionRepresenterKoszul_comp_zero R U q f hcomm)

/-- Injectivity of the first Koszul differential is exactly the leftmost
exactness assertion used by the degree-two resolution. -/
theorem sectionRepresenterKoszul_zero_left_exact
    (U : C) (q f : R.val.obj (op U))
    [Mono (sectionRepresenterKoszulFirst R U q f)] :
    (ShortComplex.mk
      (0 : (0 : SheafOfModules.{u} R) ⟶ P⟦U⟧)
      (sectionRepresenterKoszulFirst R U q f) zero_comp).Exact := by
  apply (ShortComplex.exact_iff_mono _ rfl).2
  infer_instance

/-- The map from the last section representer to a sheaf section supported on
the common zero locus of `q` and `f`. -/
noncomputable def sectionRepresenterKoszulAugmentation
    (U : C) (M : SheafOfModules.{u} R) (m : M.val.obj (op U)) :
    P⟦U⟧ ⟶ M :=
  sectionRepresenterAugmentation R U M m

/-- If both equations annihilate the represented section, the last Koszul
differential followed by the augmentation is zero. -/
theorem sectionRepresenterKoszulLast_comp_augmentation
    (U : C) (q f : R.val.obj (op U))
    (M : SheafOfModules.{u} R) (m : M.val.obj (op U))
    (hq : q • m = 0) (hf : f • m = 0) :
    sectionRepresenterKoszulLast R U q f ≫
      sectionRepresenterKoszulAugmentation R U M m = 0 := by
  apply biproduct.hom_ext'
  intro j
  fin_cases j
  · rw [sectionRepresenterKoszulLast, biproduct.ι_desc_assoc]
    change sectionRepresenterScalarEndomorphism R U q ≫
      sectionRepresenterAugmentation R U M m = 0
    rw [sectionRepresenterScalarEndomorphism_comp_augmentation, hq,
      sectionRepresenterAugmentation_zero]
  · rw [sectionRepresenterKoszulLast, biproduct.ι_desc_assoc]
    change sectionRepresenterScalarEndomorphism R U f ≫
      sectionRepresenterAugmentation R U M m = 0
    rw [sectionRepresenterScalarEndomorphism_comp_augmentation, hf,
      sectionRepresenterAugmentation_zero]

/-- The augmented last two terms of the section-representer Koszul
resolution.  Exactness is supplied separately from the regularity of the two
local equations. -/
noncomputable def sectionRepresenterKoszulAugmentedShortComplex
    (U : C) (q f : R.val.obj (op U))
    (M : SheafOfModules.{u} R) (m : M.val.obj (op U))
    (hq : q • m = 0) (hf : f • m = 0) :
    ShortComplex (SheafOfModules.{u} R) :=
  ShortComplex.mk
    (sectionRepresenterKoszulLast R U q f)
    (sectionRepresenterKoszulAugmentation R U M m)
    (sectionRepresenterKoszulLast_comp_augmentation R U q f M m hq hf)

/-- The degree-two Hom differential associated with the first Koszul map is
the expected linear combination of the two component sections. -/
theorem sectionRepresenterKoszulFirst_hom_coordinate
    (U : C) (q f : R.val.obj (op U))
    (M : SheafOfModules.{u} R)
    (h : (⨁ sectionRepresenterKoszulPair R U) ⟶ M) :
    sectionRepresenterHomAddEquiv R U M
        (sectionRepresenterKoszulFirst R U q f ≫ h) =
      (-f) • sectionRepresenterHomAddEquiv R U M
          (biproduct.ι (sectionRepresenterKoszulPair R U) 0 ≫ h) +
        q • sectionRepresenterHomAddEquiv R U M
          (biproduct.ι (sectionRepresenterKoszulPair R U) 1 ≫ h) := by
  let c : ∀ j, sectionRepresenterKoszulPair R U j ⟶ M :=
    fun j ↦ biproduct.ι (sectionRepresenterKoszulPair R U) j ≫ h
  have hh : h = biproduct.desc c := by
    apply biproduct.hom_ext'
    intro j
    rw [biproduct.ι_desc]
  rw [hh, sectionRepresenterKoszulFirst, biproduct.lift_desc]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_add, biproduct.ι_desc]
  rw [sectionRepresenterHomAddEquiv_scalarEndomorphism_comp,
    sectionRepresenterHomAddEquiv_scalarEndomorphism_comp]

end PfaffianDescent

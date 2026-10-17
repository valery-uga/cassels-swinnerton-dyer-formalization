import PfaffianDescent.CorayCechIntersectionHomTerms
import Mathlib.Algebra.BigOperators.Fin

/-! SOURCE ONLY / UNVERIFIED. The literal intersection cochains compare
with the existing actual categorical section-representer Čech Hom complex.
The all-C¹ contraction supplies both a Hom-level contracting identity and
degree-one exactness. This is not an Ext-H¹ vanishing assertion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators
universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) {ι : Type u}

private def schemeModuleCechFaceSection (V : ι → X.Opens) (n : ℕ)
    (a : Fin (n + 2))
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X n ⟶ M)
    (f : Fin (n + 2) → ι) :
    SchemeModuleOpenSectionsOver pi M (∏ᶜ fun b : Fin (n + 2) => V (f b)) :=
  let d := (FormalCoproduct.mk _ V).cech.map (SimplexCategory.δ a).op
  M.val.map (d.φ f).op
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M n h (d.f f))

private theorem schemeModuleCechFace_zero_zero (V : ι → X.Opens)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X 0 ⟶ M) (i j : ι) :
    schemeModule_openEqSectionsLinearEquiv pi M
        (schemeOpenCechProduct_one_eq V ![i, j])
        (schemeModuleCechFaceSection pi M V 0 0 h ![i, j]) =
      schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right
        (schemeModuleCechHomZeroAddEquiv pi M V h j) := by
  let d := (FormalCoproduct.mk _ V).cech.map (SimplexCategory.δ (0 : Fin 2)).op
  let g := d.f ![i, j]
  have hn := schemeModule_openEqSectionsLinearEquiv_naturality pi M
    (schemeOpenCechProduct_zero_eq V g) (schemeOpenCechProduct_one_eq V ![i, j])
    (d.φ ![i, j])
    (show V i ⊓ V j ≤ V (g 0) from inf_le_right)
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h g)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![i, j])
      (M.val.map (d.φ ![i, j]).op
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h g)) = _
  refine hn.trans (congrArg
    (schemeModuleOpenSectionsRestrictionLinearMap pi M
      (show V i ⊓ V j ≤ V (g 0) from inf_le_right)) ?_)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V g)
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h g) =
    schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V ![j])
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h ![j])
  have hs := (schemeModuleCechTupleZeroLinearEquiv pi M V).symm_apply_apply
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h)
  have ht := congrArg (schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_zero_eq V g)) (congr_fun hs g)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V g)
      ((schemeModule_openEqSectionsLinearEquiv pi M
        (schemeOpenCechProduct_zero_eq V g)).symm
        (schemeModule_openEqSectionsLinearEquiv pi M
          (schemeOpenCechProduct_zero_eq V ![j])
          (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h ![j]))) =
    schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V g)
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h g) at ht
  rw [LinearEquiv.apply_symm_apply] at ht
  exact ht.symm

private theorem schemeModuleCechFace_zero_one (V : ι → X.Opens)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X 0 ⟶ M) (i j : ι) :
    schemeModule_openEqSectionsLinearEquiv pi M
        (schemeOpenCechProduct_one_eq V ![i, j])
        (schemeModuleCechFaceSection pi M V 0 1 h ![i, j]) =
      schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_left
        (schemeModuleCechHomZeroAddEquiv pi M V h i) := by
  let d := (FormalCoproduct.mk _ V).cech.map (SimplexCategory.δ (1 : Fin 2)).op
  let g := d.f ![i, j]
  have hn := schemeModule_openEqSectionsLinearEquiv_naturality pi M
    (schemeOpenCechProduct_zero_eq V g) (schemeOpenCechProduct_one_eq V ![i, j])
    (d.φ ![i, j])
    (show V i ⊓ V j ≤ V (g 0) from inf_le_left)
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h g)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![i, j])
      (M.val.map (d.φ ![i, j]).op
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h g)) = _
  refine hn.trans (congrArg
    (schemeModuleOpenSectionsRestrictionLinearMap pi M
      (show V i ⊓ V j ≤ V (g 0) from inf_le_left)) ?_)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V g)
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h g) =
    schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V ![i])
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h ![i])
  have hs := (schemeModuleCechTupleZeroLinearEquiv pi M V).symm_apply_apply
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h)
  have ht := congrArg (schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_zero_eq V g)) (congr_fun hs g)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V g)
      ((schemeModule_openEqSectionsLinearEquiv pi M
        (schemeOpenCechProduct_zero_eq V g)).symm
        (schemeModule_openEqSectionsLinearEquiv pi M
          (schemeOpenCechProduct_zero_eq V ![i])
          (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h ![i]))) =
    schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_zero_eq V g)
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 0 h g) at ht
  rw [LinearEquiv.apply_symm_apply] at ht
  exact ht.symm

private theorem schemeModuleCechFace_one_zero (V : ι → X.Opens)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X 1 ⟶ M) (i j k : ι) :
    schemeModule_openEqSectionsLinearEquiv pi M
        (schemeOpenCechProduct_two_eq V ![i, j, k])
        (schemeModuleCechFaceSection pi M V 1 0 h ![i, j, k]) =
      schemeModuleOpenSectionsRestrictionLinearMap pi M inf_le_right
        (schemeModuleCechHomOneAddEquiv pi M V h j k) := by
  let d := (FormalCoproduct.mk _ V).cech.map (SimplexCategory.δ (0 : Fin 3)).op
  let g := d.f ![i, j, k]
  have hn := schemeModule_openEqSectionsLinearEquiv_naturality pi M
    (schemeOpenCechProduct_one_eq V g) (schemeOpenCechProduct_two_eq V ![i, j, k])
    (d.φ ![i, j, k])
    (show V i ⊓ (V j ⊓ V k) ≤ V (g 0) ⊓ V (g 1) from inf_le_right)
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_two_eq V ![i, j, k])
      (M.val.map (d.φ ![i, j, k]).op
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g)) = _
  refine hn.trans (congrArg
    (schemeModuleOpenSectionsRestrictionLinearMap pi M
      (show V i ⊓ (V j ⊓ V k) ≤ V (g 0) ⊓ V (g 1) from inf_le_right)) ?_)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V g)
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g) =
    schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![j, k])
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h ![j, k])
  have hs := (schemeModuleCechTupleOneLinearEquiv pi M V).symm_apply_apply
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h)
  have ht := congrArg (schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_one_eq V g)) (congr_fun hs g)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V g)
      ((schemeModule_openEqSectionsLinearEquiv pi M
        (schemeOpenCechProduct_one_eq V g)).symm
        (schemeModule_openEqSectionsLinearEquiv pi M
          (schemeOpenCechProduct_one_eq V ![j, k])
          (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h ![j, k]))) =
    schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V g)
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g) at ht
  rw [LinearEquiv.apply_symm_apply] at ht
  exact ht.symm

private theorem schemeModuleCechFace_one_one (V : ι → X.Opens)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X 1 ⟶ M) (i j k : ι) :
    schemeModule_openEqSectionsLinearEquiv pi M
        (schemeOpenCechProduct_two_eq V ![i, j, k])
        (schemeModuleCechFaceSection pi M V 1 1 h ![i, j, k]) =
      schemeModuleOpenSectionsRestrictionLinearMap pi M
        (inf_le_inf_left (V i) inf_le_right)
        (schemeModuleCechHomOneAddEquiv pi M V h i k) := by
  let d := (FormalCoproduct.mk _ V).cech.map (SimplexCategory.δ (1 : Fin 3)).op
  let g := d.f ![i, j, k]
  have hn := schemeModule_openEqSectionsLinearEquiv_naturality pi M
    (schemeOpenCechProduct_one_eq V g) (schemeOpenCechProduct_two_eq V ![i, j, k])
    (d.φ ![i, j, k])
    (show V i ⊓ (V j ⊓ V k) ≤ V (g 0) ⊓ V (g 1) from
      inf_le_inf_left (V i) inf_le_right)
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_two_eq V ![i, j, k])
      (M.val.map (d.φ ![i, j, k]).op
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g)) = _
  refine hn.trans (congrArg
    (schemeModuleOpenSectionsRestrictionLinearMap pi M
      (show V i ⊓ (V j ⊓ V k) ≤ V (g 0) ⊓ V (g 1) from inf_le_inf_left (V i) inf_le_right)) ?_)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V g)
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g) =
    schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![i, k])
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h ![i, k])
  have hs := (schemeModuleCechTupleOneLinearEquiv pi M V).symm_apply_apply
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h)
  have ht := congrArg (schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_one_eq V g)) (congr_fun hs g)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V g)
      ((schemeModule_openEqSectionsLinearEquiv pi M
        (schemeOpenCechProduct_one_eq V g)).symm
        (schemeModule_openEqSectionsLinearEquiv pi M
          (schemeOpenCechProduct_one_eq V ![i, k])
          (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h ![i, k]))) =
    schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V g)
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g) at ht
  rw [LinearEquiv.apply_symm_apply] at ht
  exact ht.symm

private theorem schemeModuleCechFace_one_two (V : ι → X.Opens)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X 1 ⟶ M) (i j k : ι) :
    schemeModule_openEqSectionsLinearEquiv pi M
        (schemeOpenCechProduct_two_eq V ![i, j, k])
        (schemeModuleCechFaceSection pi M V 1 2 h ![i, j, k]) =
      schemeModuleOpenSectionsRestrictionLinearMap pi M
        (inf_le_inf_left (V i) inf_le_left)
        (schemeModuleCechHomOneAddEquiv pi M V h i j) := by
  let d := (FormalCoproduct.mk _ V).cech.map (SimplexCategory.δ (2 : Fin 3)).op
  let g := d.f ![i, j, k]
  have hn := schemeModule_openEqSectionsLinearEquiv_naturality pi M
    (schemeOpenCechProduct_one_eq V g) (schemeOpenCechProduct_two_eq V ![i, j, k])
    (d.φ ![i, j, k])
    (show V i ⊓ (V j ⊓ V k) ≤ V (g 0) ⊓ V (g 1) from
      inf_le_inf_left (V i) inf_le_left)
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_two_eq V ![i, j, k])
      (M.val.map (d.φ ![i, j, k]).op
        (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g)) = _
  refine hn.trans (congrArg
    (schemeModuleOpenSectionsRestrictionLinearMap pi M
      (show V i ⊓ (V j ⊓ V k) ≤ V (g 0) ⊓ V (g 1) from inf_le_inf_left (V i) inf_le_left)) ?_)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V g)
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g) =
    schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![i, j])
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h ![i, j])
  have hs := (schemeModuleCechTupleOneLinearEquiv pi M V).symm_apply_apply
    (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h)
  have ht := congrArg (schemeModule_openEqSectionsLinearEquiv pi M
    (schemeOpenCechProduct_one_eq V g)) (congr_fun hs g)
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V g)
      ((schemeModule_openEqSectionsLinearEquiv pi M
        (schemeOpenCechProduct_one_eq V g)).symm
        (schemeModule_openEqSectionsLinearEquiv pi M
          (schemeOpenCechProduct_one_eq V ![i, j])
          (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h ![i, j]))) =
    schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V g)
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1 h g) at ht
  rw [LinearEquiv.apply_symm_apply] at ht
  exact ht.symm

/-- The first actual categorical Hom differential is the original-K
linear alternating restriction on literal pair intersections. -/
theorem schemeModuleCechHomZeroAddEquiv_d (V : ι → X.Opens)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X 0 ⟶ M) :
    schemeModuleCechHomOneAddEquiv pi M V
        ((sectionRepresenterCechChain X.ringCatSheaf V).d 1 0 ≫ h) =
      schemeModuleCechZeroDifferential pi M V
        (schemeModuleCechHomZeroAddEquiv pi M V h) := by
  funext i j
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![i, j])
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 1
        ((sectionRepresenterCechChain X.ringCatSheaf V).d 1 0 ≫ h) ![i, j]) = _
  rw [sectionRepresenterCechHomEquivPi_d]
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_one_eq V ![i, j])
      (∑ a : Fin 2, (-1 : ℤ) ^ (a : ℕ) •
        schemeModuleCechFaceSection pi M V 0 a h ![i, j]) = _
  rw [map_sum, Fin.sum_univ_two]
  simp only [map_neg, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul]
  rw [schemeModuleCechFace_zero_zero, schemeModuleCechFace_zero_one] <;>
    simp only [schemeModuleCechZeroDifferential, sub_eq_add_neg] <;> rfl

/-- The second actual categorical Hom differential is the original-K
linear alternating restriction on literal triple intersections. -/
theorem schemeModuleCechHomOneAddEquiv_d (V : ι → X.Opens)
    (h : (sectionRepresenterCechChain X.ringCatSheaf V).X 1 ⟶ M) :
    schemeModuleCechHomTwoAddEquiv pi M V
        ((sectionRepresenterCechChain X.ringCatSheaf V).d 2 1 ≫ h) =
      schemeModuleCechOneDifferential pi M V
        (schemeModuleCechHomOneAddEquiv pi M V h) := by
  funext i j k
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_two_eq V ![i, j, k])
      (sectionRepresenterCechHomEquivPi X.ringCatSheaf V M 2
        ((sectionRepresenterCechChain X.ringCatSheaf V).d 2 1 ≫ h) ![i, j, k]) = _
  rw [sectionRepresenterCechHomEquivPi_d]
  change schemeModule_openEqSectionsLinearEquiv pi M
      (schemeOpenCechProduct_two_eq V ![i, j, k])
      (∑ a : Fin 3, (-1 : ℤ) ^ (a : ℕ) •
        schemeModuleCechFaceSection pi M V 1 a h ![i, j, k]) = _
  rw [map_sum, Fin.sum_univ_three]
  have hv2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simp only [map_neg, Fin.val_zero, Fin.val_one, hv2,
    pow_zero, pow_one, neg_one_sq, one_zsmul, neg_one_zsmul]
  rw [schemeModuleCechFace_one_zero, schemeModuleCechFace_one_one,
    schemeModuleCechFace_one_two] <;>
    simp only [schemeModuleCechOneDifferential, sub_eq_add_neg, add_assoc] <;> rfl

/-- The explicit section contraction, transported through actual Yoneda
and intersection identifications, is a morphism-valued primitive. -/
def schemeModule_augmentedCechHomOneContraction
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U) :
    ((sectionRepresenterCechChain X.ringCatSheaf
      (supportAugmentedOpenFamily U V)).X 1 ⟶ M) →+
    ((sectionRepresenterCechChain X.ringCatSheaf
      (supportAugmentedOpenFamily U V)).X 0 ⟶ M) :=
  (schemeModuleCechHomZeroAddEquiv pi M (supportAugmentedOpenFamily U V)).symm.toAddMonoidHom.comp
    ((schemeModule_augmentedCechOneContraction pi M U V C hC hsupport hCU).toAddMonoidHom.comp
      (schemeModuleCechHomOneAddEquiv pi M (supportAugmentedOpenFamily U V)).toAddMonoidHom)

def schemeModule_augmentedCechHomTwoContraction
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U) :
    ((sectionRepresenterCechChain X.ringCatSheaf
      (supportAugmentedOpenFamily U V)).X 2 ⟶ M) →+
    ((sectionRepresenterCechChain X.ringCatSheaf
      (supportAugmentedOpenFamily U V)).X 1 ⟶ M) :=
  (schemeModuleCechHomOneAddEquiv pi M (supportAugmentedOpenFamily U V)).symm.toAddMonoidHom.comp
    ((schemeModule_augmentedCechTwoContraction pi M U V C hC hsupport hCU).toAddMonoidHom.comp
      (schemeModuleCechHomTwoAddEquiv pi M (supportAugmentedOpenFamily U V)).toAddMonoidHom)

theorem schemeModule_augmentedCechHomOne_homotopy_identity
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U)
    (h : (sectionRepresenterCechChain X.ringCatSheaf
      (supportAugmentedOpenFamily U V)).X 1 ⟶ M) :
    (sectionRepresenterCechChain X.ringCatSheaf
        (supportAugmentedOpenFamily U V)).d 1 0 ≫
        schemeModule_augmentedCechHomOneContraction pi M U V C hC hsupport hCU h +
      schemeModule_augmentedCechHomTwoContraction pi M U V C hC hsupport hCU
        ((sectionRepresenterCechChain X.ringCatSheaf
          (supportAugmentedOpenFamily U V)).d 2 1 ≫ h) = h := by
  let A := supportAugmentedOpenFamily U V
  apply (schemeModuleCechHomOneAddEquiv pi M A).injective
  rw [map_add, schemeModuleCechHomZeroAddEquiv_d]
  change schemeModuleCechZeroDifferential pi M A
      ((schemeModuleCechHomZeroAddEquiv pi M A)
        ((schemeModuleCechHomZeroAddEquiv pi M A).symm
          (schemeModule_augmentedCechOneContraction pi M U V C hC hsupport hCU
            (schemeModuleCechHomOneAddEquiv pi M A h)))) +
    (schemeModuleCechHomOneAddEquiv pi M A)
      ((schemeModuleCechHomOneAddEquiv pi M A).symm
        (schemeModule_augmentedCechTwoContraction pi M U V C hC hsupport hCU
          (schemeModuleCechHomTwoAddEquiv pi M A
            ((sectionRepresenterCechChain X.ringCatSheaf A).d 2 1 ≫ h)))) =
    schemeModuleCechHomOneAddEquiv pi M A h
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    schemeModuleCechHomOneAddEquiv_d]
  exact schemeModule_augmentedCechOne_homotopy_identity pi M U V C hC hsupport hCU _

include pi in
/-- Exactness for the actual categorical Hom complex in degree one.
The only support hypothesis is closed support contained in the actual
distinguished open; acyclicity is a conclusion, never an input. -/
theorem schemeModule_augmentedCechHom_exact_one_of_closedSupport_subset
    (U : X.Opens) (V : ι → X.Opens) (C : Set X) (hC : IsClosed C)
    (hsupport : schemeModuleStalkSupport M ⊆ C) (hCU : C ⊆ U) :
    Function.Exact
      (fun h : (sectionRepresenterCechChain X.ringCatSheaf
          (supportAugmentedOpenFamily U V)).X 0 ⟶ M =>
        (sectionRepresenterCechChain X.ringCatSheaf
          (supportAugmentedOpenFamily U V)).d 1 0 ≫ h)
      (fun h : (sectionRepresenterCechChain X.ringCatSheaf
          (supportAugmentedOpenFamily U V)).X 1 ⟶ M =>
        (sectionRepresenterCechChain X.ringCatSheaf
          (supportAugmentedOpenFamily U V)).d 2 1 ≫ h) := by
  intro h
  constructor
  · intro hh
    change (sectionRepresenterCechChain X.ringCatSheaf
      (supportAugmentedOpenFamily U V)).d 2 1 ≫ h = 0 at hh
    refine ⟨schemeModule_augmentedCechHomOneContraction pi M U V C hC hsupport hCU h, ?_⟩
    have hi := schemeModule_augmentedCechHomOne_homotopy_identity
      pi M U V C hC hsupport hCU h
    rw [hh, map_zero, add_zero] at hi
    exact hi
  · rintro ⟨a, rfl⟩
    change (sectionRepresenterCechChain X.ringCatSheaf
      (supportAugmentedOpenFamily U V)).d 2 1 ≫
      ((sectionRepresenterCechChain X.ringCatSheaf
        (supportAugmentedOpenFamily U V)).d 1 0 ≫ a) = 0
    rw [← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]

end PfaffianDescent.Coray

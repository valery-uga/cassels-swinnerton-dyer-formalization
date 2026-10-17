import PfaffianDescent.SectionRepresenterCechHomDifferential

/-!
# Scalar endomorphisms of a section representer

The sheaf representing sections on an open carries a canonical generator on
that open.  Multiplying this generator by a local ring section and applying
Yoneda gives the corresponding scalar endomorphism.  These maps are the
entries of the affine Koszul resolution used for the closed-point Ext
calculation in Voisin's Serre-duality argument.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace PfaffianDescent

universe u

variable {C : Type u} [SmallCategory C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The universal section of the object representing sections on `U`. -/
noncomputable def sectionRepresenterGenerator (U : C) :
    (sectionRepresenter R U).val.obj (op U) :=
  sectionRepresenterHomEquiv R U (sectionRepresenter R U) (𝟙 _)

/-- Scalar multiplication by a ring section on the universal generator. -/
noncomputable def sectionRepresenterScalarEndomorphism (U : C)
    (a : R.val.obj (op U)) :
    sectionRepresenter R U ⟶ sectionRepresenter R U :=
  (sectionRepresenterHomEquiv R U (sectionRepresenter R U)).symm
    (a • sectionRepresenterGenerator R U)

@[simp]
theorem sectionRepresenterHomEquiv_scalarEndomorphism (U : C)
    (a : R.val.obj (op U)) :
    sectionRepresenterHomEquiv R U (sectionRepresenter R U)
        (sectionRepresenterScalarEndomorphism R U a) =
      a • sectionRepresenterGenerator R U := by
  exact Equiv.apply_symm_apply _ _

/-- Yoneda coordinates turn postcomposition into evaluation of the
postcomposed morphism on the represented section. -/
theorem sectionRepresenterHomEquiv_postcomp
    (U : C) {M N : SheafOfModules.{u} R}
    (f : sectionRepresenter R U ⟶ M) (g : M ⟶ N) :
    sectionRepresenterHomEquiv R U N (f ≫ g) =
      g.val.app (op U) (sectionRepresenterHomEquiv R U M f) := by
  rfl

/-- A morphism out of a section representer is recovered by evaluating it
on the universal generator. -/
theorem sectionRepresenterHom_apply_generator
    (U : C) {M : SheafOfModules.{u} R}
    (g : sectionRepresenter R U ⟶ M) :
    g.val.app (op U) (sectionRepresenterGenerator R U) =
      sectionRepresenterHomEquiv R U M g := by
  have h := sectionRepresenterHomEquiv_postcomp R U (M := sectionRepresenter R U)
    (N := M) (𝟙 _) g
  simpa [sectionRepresenterGenerator] using h.symm

/-- The morphism represented by a section on `U`.  This is the augmentation
used when a local pair of equations cuts out a point. -/
noncomputable def sectionRepresenterAugmentation
    (U : C) (M : SheafOfModules.{u} R) (m : M.val.obj (op U)) :
    sectionRepresenter R U ⟶ M :=
  (sectionRepresenterHomEquiv R U M).symm m

@[simp]
theorem sectionRepresenterHomEquiv_augmentation
    (U : C) (M : SheafOfModules.{u} R) (m : M.val.obj (op U)) :
    sectionRepresenterHomEquiv R U M
        (sectionRepresenterAugmentation R U M m) = m := by
  exact Equiv.apply_symm_apply _ _

@[simp]
theorem sectionRepresenterHomAddEquiv_augmentation
    (U : C) (M : SheafOfModules.{u} R) (m : M.val.obj (op U)) :
    sectionRepresenterHomAddEquiv R U M
        (sectionRepresenterAugmentation R U M m) = m := by
  exact sectionRepresenterHomEquiv_augmentation R U M m

@[simp]
theorem sectionRepresenterAugmentation_zero
    (U : C) (M : SheafOfModules.{u} R) :
    sectionRepresenterAugmentation R U M 0 = 0 := by
  unfold sectionRepresenterAugmentation
  exact (sectionRepresenterHomAddEquiv R U M).symm.map_zero

theorem sectionRepresenterAugmentation_add
    (U : C) (M : SheafOfModules.{u} R) (m n : M.val.obj (op U)) :
    sectionRepresenterAugmentation R U M (m + n) =
      sectionRepresenterAugmentation R U M m +
        sectionRepresenterAugmentation R U M n := by
  unfold sectionRepresenterAugmentation
  exact (sectionRepresenterHomAddEquiv R U M).symm.map_add m n

/-- Precomposing a represented section by a scalar endomorphism multiplies
that section by the scalar. -/
theorem sectionRepresenterScalarEndomorphism_comp_augmentation
    (U : C) (M : SheafOfModules.{u} R)
    (a : R.val.obj (op U)) (m : M.val.obj (op U)) :
    sectionRepresenterScalarEndomorphism R U a ≫
        sectionRepresenterAugmentation R U M m =
      sectionRepresenterAugmentation R U M (a • m) := by
  apply (sectionRepresenterHomEquiv R U M).injective
  rw [sectionRepresenterHomEquiv_postcomp,
    sectionRepresenterHomEquiv_scalarEndomorphism, map_smul,
    sectionRepresenterHom_apply_generator,
    sectionRepresenterHomEquiv_augmentation,
    sectionRepresenterHomEquiv_augmentation]

/-- In Yoneda coordinates, precomposition by the scalar endomorphism is
scalar multiplication on sections. -/
theorem sectionRepresenterHomEquiv_scalarEndomorphism_comp
    (U : C) (M : SheafOfModules.{u} R)
    (a : R.val.obj (op U)) (g : sectionRepresenter R U ⟶ M) :
    sectionRepresenterHomEquiv R U M
        (sectionRepresenterScalarEndomorphism R U a ≫ g) =
      a • sectionRepresenterHomEquiv R U M g := by
  rw [sectionRepresenterHomEquiv_postcomp,
    sectionRepresenterHomEquiv_scalarEndomorphism, map_smul,
    sectionRepresenterHom_apply_generator]

theorem sectionRepresenterHomAddEquiv_scalarEndomorphism_comp
    (U : C) (M : SheafOfModules.{u} R)
    (a : R.val.obj (op U)) (g : sectionRepresenter R U ⟶ M) :
    sectionRepresenterHomAddEquiv R U M
        (sectionRepresenterScalarEndomorphism R U a ≫ g) =
      a • sectionRepresenterHomAddEquiv R U M g := by
  exact sectionRepresenterHomEquiv_scalarEndomorphism_comp R U M a g

@[simp]
theorem sectionRepresenterScalarEndomorphism_zero (U : C) :
    sectionRepresenterScalarEndomorphism R U 0 = 0 := by
  let E := sectionRepresenterHomAddEquiv R U (sectionRepresenter R U)
  apply E.injective
  change E (E.symm (0 • sectionRepresenterGenerator R U)) = E 0
  rw [E.apply_symm_apply, E.map_zero, zero_smul]

theorem sectionRepresenterScalarEndomorphism_add
    (U : C) (a b : R.val.obj (op U)) :
    sectionRepresenterScalarEndomorphism R U (a + b) =
      sectionRepresenterScalarEndomorphism R U a +
        sectionRepresenterScalarEndomorphism R U b := by
  let E := sectionRepresenterHomAddEquiv R U (sectionRepresenter R U)
  apply E.injective
  change E (E.symm ((a + b) • sectionRepresenterGenerator R U)) =
    E (E.symm (a • sectionRepresenterGenerator R U) +
      E.symm (b • sectionRepresenterGenerator R U))
  rw [E.apply_symm_apply, E.map_add, E.apply_symm_apply,
    E.apply_symm_apply, add_smul]

@[simp]
theorem sectionRepresenterScalarEndomorphism_neg
    (U : C) (a : R.val.obj (op U)) :
    sectionRepresenterScalarEndomorphism R U (-a) =
      -sectionRepresenterScalarEndomorphism R U a := by
  let E := sectionRepresenterHomAddEquiv R U (sectionRepresenter R U)
  apply E.injective
  change E (E.symm ((-a) • sectionRepresenterGenerator R U)) =
    E (-E.symm (a • sectionRepresenterGenerator R U))
  rw [E.apply_symm_apply, E.map_neg, E.apply_symm_apply, neg_smul]

@[simp]
theorem sectionRepresenterScalarEndomorphism_one (U : C) :
    sectionRepresenterScalarEndomorphism R U 1 = 𝟙 _ := by
  apply (sectionRepresenterHomEquiv R U (sectionRepresenter R U)).injective
  simp [sectionRepresenterScalarEndomorphism, sectionRepresenterGenerator]

/-- Scalar endomorphisms compose by multiplication of their local
coefficients. -/
theorem sectionRepresenterScalarEndomorphism_comp
    (U : C) (a b : R.val.obj (op U)) :
    sectionRepresenterScalarEndomorphism R U a ≫
        sectionRepresenterScalarEndomorphism R U b =
      sectionRepresenterScalarEndomorphism R U (a * b) := by
  apply (sectionRepresenterHomEquiv R U (sectionRepresenter R U)).injective
  rw [sectionRepresenterHomEquiv_postcomp,
    sectionRepresenterHomEquiv_scalarEndomorphism,
    sectionRepresenterHomEquiv_scalarEndomorphism]
  rw [map_smul, sectionRepresenterHom_apply_generator,
    sectionRepresenterHomEquiv_scalarEndomorphism]
  exact (mul_smul a b (sectionRepresenterGenerator R U)).symm

end PfaffianDescent

import PfaffianDescent.VoisinCubicQuotientCechDifferential

/-!
# Raw cubic-quotient Cech cocycles and actual second cohomology

The differential-compatible termwise Yoneda equivalence restricts to an
additive equivalence between raw degree-two Cech cocycles and the abstract
Hom cocycles used by the verified degree-two Cech-to-Ext comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

lemma cubicQuotientSectionRepresenterCechHomEquiv_zero
    (I : HomogeneousIdeal PS) (m n : ℕ) :
    cubicQuotientSectionRepresenterCechHomEquiv K I m n
      (0 : (quotientSectionRepresenterCechChain I).X n ⟶
        sheafOfModules (grading I) m) = 0 :=
  smallCoverSectionHomEquiv_zero (Proj (grading I)).ringCatSheaf
    (quotientCoordinateOpen I) (sheafOfModules (grading I) m) n

lemma cubicQuotientSectionRepresenterCechHomEquiv_add
    (I : HomogeneousIdeal PS) (m n : ℕ)
    (x y : (quotientSectionRepresenterCechChain I).X n ⟶
      sheafOfModules (grading I) m) :
    cubicQuotientSectionRepresenterCechHomEquiv K I m n (x + y) =
      cubicQuotientSectionRepresenterCechHomEquiv K I m n x +
        cubicQuotientSectionRepresenterCechHomEquiv K I m n y :=
  smallCoverSectionHomEquiv_add (Proj (grading I)).ringCatSheaf
    (quotientCoordinateOpen I) (sheafOfModules (grading I) m) n x y

/-- Raw degree-two Cech cocycles on the four quotient-coordinate opens. -/
abbrev CubicQuotientRawDegreeTwoCocycle
    (I : HomogeneousIdeal PS) (m : ℕ) :=
  AddMonoidHom.ker ((quotientNegativeTwistCechComplex I m).d 2 3).hom

/-- Transport an abstract section-representer Hom cocycle to a raw Cech
cocycle. -/
def cubicQuotientRawCocycleOfAbstract
    (I : HomogeneousIdeal PS) (m : ℕ)
    (f : QuotientCechDegreeTwoCocycle I m) :
    CubicQuotientRawDegreeTwoCocycle K I m := by
  refine ⟨cubicQuotientSectionRepresenterCechHomEquiv K I m 2 f.1, ?_⟩
  change (quotientNegativeTwistCechComplex I m).d 2 3
    (cubicQuotientSectionRepresenterCechHomEquiv K I m 2 f.1) = 0
  have hf : (quotientSectionRepresenterCechChain I).d 3 2 ≫ f.1 = 0 := f.2
  rw [← cubicQuotientSectionRepresenterCechHomEquiv_d, hf,
    cubicQuotientSectionRepresenterCechHomEquiv_zero]

/-- Transport a raw degree-two Cech cocycle back to the abstract Hom
cocycle used in the Cech-to-Ext comparison. -/
def cubicQuotientAbstractCocycleOfRaw
    (I : HomogeneousIdeal PS) (m : ℕ)
    (w : CubicQuotientRawDegreeTwoCocycle K I m) :
    QuotientCechDegreeTwoCocycle I m := by
  let h := (cubicQuotientSectionRepresenterCechHomEquiv K I m 2).symm w.1
  refine ⟨h, ?_⟩
  change (quotientSectionRepresenterCechChain I).d 3 2 ≫ h = 0
  apply (cubicQuotientSectionRepresenterCechHomEquiv K I m 3).injective
  rw [cubicQuotientSectionRepresenterCechHomEquiv_d,
    Equiv.apply_symm_apply, w.2,
    cubicQuotientSectionRepresenterCechHomEquiv_zero]

/-- Raw and abstract degree-two Cech cocycles are additively equivalent. -/
noncomputable def cubicQuotientDegreeTwoCocycleEquivRaw
    (I : HomogeneousIdeal PS) (m : ℕ) :
    QuotientCechDegreeTwoCocycle I m ≃+
      CubicQuotientRawDegreeTwoCocycle K I m where
  toFun := cubicQuotientRawCocycleOfAbstract K I m
  invFun := cubicQuotientAbstractCocycleOfRaw K I m
  left_inv f := by
    apply Subtype.ext
    exact (cubicQuotientSectionRepresenterCechHomEquiv K I m 2).symm_apply_apply f.1
  right_inv w := by
    apply Subtype.ext
    exact (cubicQuotientSectionRepresenterCechHomEquiv K I m 2).apply_symm_apply w.1
  map_add' f g := by
    apply Subtype.ext
    exact cubicQuotientSectionRepresenterCechHomEquiv_add K I m 2 f.1 g.1

/-- A raw degree-two cocycle determines actual `Ext²` from the augmentation
target. -/
noncomputable def cubicQuotientRawDegreeTwoToAugmentedExtHom
    (I : HomogeneousIdeal PS)
    [HasExt.{u} (Proj (grading I)).Modules] (m : ℕ) :
    CubicQuotientRawDegreeTwoCocycle K I m →+
      Ext.{u} (quotientSectionRepresenterCechTarget I)
        (sheafOfModules (grading I) m) 2 :=
  (quotientCechDegreeTwoToAugmentedExtHom I m).comp
    (cubicQuotientDegreeTwoCocycleEquivRaw K I m).symm.toAddMonoidHom

/-- Every augmented `Ext²` class is represented by a raw degree-two Cech
cocycle. -/
theorem cubicQuotientRawDegreeTwoToAugmentedExt_surjective
    (I : HomogeneousIdeal PS)
    [HasExt.{u} (Proj (grading I)).Modules] (m : ℕ) :
    Function.Surjective
      (cubicQuotientRawDegreeTwoToAugmentedExtHom K I m) := by
  intro z
  obtain ⟨f, hf⟩ := quotientCechDegreeTwoToAugmentedExt_surjective I m z
  refine ⟨cubicQuotientDegreeTwoCocycleEquivRaw K I m f, ?_⟩
  change quotientCechDegreeTwoToAugmentedExt I m
      ((cubicQuotientDegreeTwoCocycleEquivRaw K I m).symm
        (cubicQuotientDegreeTwoCocycleEquivRaw K I m f)) = z
  rw [AddEquiv.symm_apply_apply]
  exact hf

/-- A raw degree-two cocycle dies in actual `Ext²` exactly when it is the
raw Cech differential of a degree-one cochain. -/
theorem cubicQuotientRawDegreeTwoToAugmentedExt_eq_zero_iff
    (I : HomogeneousIdeal PS)
    [HasExt.{u} (Proj (grading I)).Modules] (m : ℕ)
    (w : CubicQuotientRawDegreeTwoCocycle K I m) :
    cubicQuotientRawDegreeTwoToAugmentedExtHom K I m w = 0 ↔
      ∃ y : (quotientNegativeTwistCechComplex I m).X 1,
        (quotientNegativeTwistCechComplex I m).d 1 2 y = w.1 := by
  let f := cubicQuotientAbstractCocycleOfRaw K I m w
  have hc := quotientCechDegreeTwoToAugmentedExt_eq_zero_iff I m f
  constructor
  · intro hw
    have hw' : quotientCechDegreeTwoToAugmentedExt I m f = 0 := by
      change quotientCechDegreeTwoToAugmentedExt I m
        (cubicQuotientAbstractCocycleOfRaw K I m w) = 0 at hw
      exact hw
    obtain ⟨q, hq⟩ := hc.mp hw'
    refine ⟨cubicQuotientSectionRepresenterCechHomEquiv K I m 1 q, ?_⟩
    rw [← cubicQuotientSectionRepresenterCechHomEquiv_d, hq]
    change cubicQuotientSectionRepresenterCechHomEquiv K I m 2
      ((cubicQuotientSectionRepresenterCechHomEquiv K I m 2).symm w.1) = w.1
    exact (cubicQuotientSectionRepresenterCechHomEquiv K I m 2).apply_symm_apply w.1
  · rintro ⟨y, hy⟩
    apply hc.mpr
    let q := (cubicQuotientSectionRepresenterCechHomEquiv K I m 1).symm y
    refine ⟨q, ?_⟩
    apply (cubicQuotientSectionRepresenterCechHomEquiv K I m 2).injective
    rw [cubicQuotientSectionRepresenterCechHomEquiv_d,
      Equiv.apply_symm_apply, hy]
    change w.1 = cubicQuotientSectionRepresenterCechHomEquiv K I m 2
      ((cubicQuotientSectionRepresenterCechHomEquiv K I m 2).symm w.1)
    exact ((cubicQuotientSectionRepresenterCechHomEquiv K I m 2).apply_symm_apply
      w.1).symm

/-- The quotient of raw degree-two Cech cocycles by the boundary kernel is
actual `Ext²` from the augmentation target. -/
noncomputable def cubicQuotientRawDegreeTwoQuotientEquivAugmentedExt
    (I : HomogeneousIdeal PS)
    [HasExt.{u} (Proj (grading I)).Modules] (m : ℕ) :
    CubicQuotientRawDegreeTwoCocycle K I m ⧸
        (cubicQuotientRawDegreeTwoToAugmentedExtHom K I m).ker ≃+
      Ext.{u} (quotientSectionRepresenterCechTarget I)
        (sheafOfModules (grading I) m) 2 :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (cubicQuotientRawDegreeTwoToAugmentedExtHom K I m)
    (cubicQuotientRawDegreeTwoToAugmentedExt_surjective K I m)

/-- The raw degree-two Cech quotient on a four-coordinate projective
quotient computes its actual second cohomology. -/
noncomputable def cubicQuotientRawDegreeTwoQuotientEquivCohomologyTwo
    (I : HomogeneousIdeal PS)
    [HasExt.{u} (Proj (grading I)).Modules] (m : ℕ) :
    CubicQuotientRawDegreeTwoCocycle K I m ⧸
        (cubicQuotientRawDegreeTwoToAugmentedExtHom K I m).ker ≃+
      schemeModuleCohomology (Proj (grading I))
        (sheafOfModules (grading I) m) 2 :=
  (cubicQuotientRawDegreeTwoQuotientEquivAugmentedExt K I m).trans
    (extPrecompIsoOfIso (quotientSectionRepresenterCechTargetIsoUnit I))

end PfaffianDescent.ProjectiveNegativeTwist

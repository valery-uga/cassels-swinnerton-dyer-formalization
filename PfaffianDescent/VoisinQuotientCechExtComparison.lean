import PfaffianDescent.CechExtDegreeTwo
import PfaffianDescent.SectionRepresenterCechLocalExact
import PfaffianDescent.SectionRepresenterCechAugmentationExact
import PfaffianDescent.SectionRepresenterTop
import PfaffianDescent.VoisinQuotientStandardOpenExtVanishing
import PfaffianDescent.VoisinTwistCechAggregate
import PfaffianDescent.VoisinSectionRepresenterCechDifferential

/-!
# Degree-two Cech-to-Ext comparison on a projective quotient

The coordinate cover of a homogeneous projective quotient gives an exact
augmented section-representer Cech chain.  Together with the affine-open
vanishing proved in `VoisinQuotientStandardOpenExtVanishing`, its Hom
cohomology in degree two computes actual `Ext²` into a negative twist.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} {sigma : Type} [Field K] [Finite sigma]

local notation "AA" => MvPolynomial.homogeneousSubmodule sigma K

/-- Delete one entry from an ordered quotient-coordinate tuple. -/
private def quotientDeleteTuple {n : ℕ} (i : Fin (n + 2))
    (f : Fin (n + 2) → sigma) : Fin (n + 1) → sigma :=
  fun j => f (i.succAbove j)

/-- The chosen categorical product of a finite family of quotient coordinate
opens is their infimum. -/
lemma quotientCechProduct_eq_inf
    (I : HomogeneousIdeal AA) (q : ℕ)
    (f : Fin (q + 1) → sigma) :
    (∏ᶜ fun a : Fin (q + 1) => quotientCoordinateOpen I (f a)) =
      (⨅ a, quotientCoordinateOpen I (f a)) := by
  apply le_antisymm
  · exact le_iInf fun a =>
      (Pi.π (fun a : Fin (q + 1) => quotientCoordinateOpen I (f a)) a).le
  · exact (Pi.lift (fun a : Fin (q + 1) => homOfLE (iInf_le _ a))).le

/-- The raw Cech complex of an intrinsic negative twist on the quotient
coordinate cover. -/
noncomputable def quotientNegativeTwistCechComplex
    (I : HomogeneousIdeal AA) (m : ℕ) :
    CochainComplex AddCommGrpCat ℕ :=
  (CategoryTheory.cechComplexFunctor (quotientCoordinateOpen I)).obj
    (modulePresheaf (grading I) m).presheaf

/-- A raw quotient Cech term is the product of the section groups on all
ordered coordinate intersections. -/
theorem quotientNegativeTwistCechComplex_X
    (I : HomogeneousIdeal AA) (m n : ℕ) :
    (quotientNegativeTwistCechComplex I m).X n =
      ∏ᶜ fun (f : Fin (n + 1) → sigma) =>
        (modulePresheaf (grading I) m).presheaf.obj
          (op (∏ᶜ fun a : Fin (n + 1) =>
            quotientCoordinateOpen I (f a))) := rfl

/-- The family of section groups making up one quotient Cech term. -/
noncomputable abbrev quotientCechTermFamily
    (I : HomogeneousIdeal AA) (m n : ℕ)
    (f : Fin (n + 1) → sigma) : AddCommGrpCat :=
  (modulePresheaf (grading I) m).presheaf.obj
    (op (∏ᶜ fun a : Fin (n + 1) => quotientCoordinateOpen I (f a)))

/-- One quotient Cech summand in its homogeneous-localization model. -/
noncomputable def quotientCechTermComponentIsoAway
    (I : HomogeneousIdeal AA) (m n : ℕ)
    (f : Fin (n + 1) → sigma) :
    quotientCechTermFamily I m n f ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away (grading I)
        (quotientCechDenominator I n f)) :=
  (modulePresheaf (grading I) m).presheaf.mapIso
      (eqToIso (quotientCechProduct_eq_inf I n f)).op.symm ≪≫
    quotientNegativeTwistCechSummandIsoAway I m n f

/-- A raw quotient Cech term is additively equivalent to its tuple of
homogeneous-localization components. -/
noncomputable def quotientNegativeTwistCechTermAddEquivAway
    (I : HomogeneousIdeal AA) (m n : ℕ) :
    (quotientNegativeTwistCechComplex I m).X n ≃+
      (∀ f : Fin (n + 1) → sigma,
        HomogeneousLocalization.Away (grading I)
          (quotientCechDenominator I n f)) :=
  (addCommGrpIsoAddEquiv
      (eqToIso (quotientNegativeTwistCechComplex_X I m n))).trans
    ((addCommGrpProductAddEquivPi (quotientCechTermFamily I m n)).trans
      (AddEquiv.piCongrRight fun f =>
        addCommGrpIsoAddEquiv (quotientCechTermComponentIsoAway I m n f)))

/-- Reindex ordered quotient-coordinate intersections between the lifted
site index and the original coordinate index. -/
private def quotientIndexFunEquiv (n : ℕ) :
    (Fin (n + 1) → ULift.{u} sigma) ≃
      (Fin (n + 1) → sigma) where
  toFun f i := (f i).down
  invFun f i := ⟨f i⟩
  left_inv f := by
    funext i
    cases h : f i
    simp [h]
  right_inv f := by funext i; rfl

/-- A raw quotient Cech term as the corresponding dependent family of
section groups. -/
noncomputable def quotientNegativeTwistCechTermEquivPi
    (I : HomogeneousIdeal AA) (m n : ℕ) :
    (quotientNegativeTwistCechComplex I m).X n ≃
      (∀ f : Fin (n + 1) → sigma, quotientCechTermFamily I m n f) :=
  ((addCommGrpIsoAddEquiv
      (eqToIso (quotientNegativeTwistCechComplex_X I m n))).trans
    (addCommGrpProductAddEquivPi (quotientCechTermFamily I m n))).toEquiv

lemma quotientNegativeTwistCechTermEquivPi_add
    (I : HomogeneousIdeal AA) (m n : ℕ)
    (x y : (quotientNegativeTwistCechComplex I m).X n) :
    quotientNegativeTwistCechTermEquivPi I m n (x + y) =
      quotientNegativeTwistCechTermEquivPi I m n x +
        quotientNegativeTwistCechTermEquivPi I m n y := by
  unfold quotientNegativeTwistCechTermEquivPi
  exact map_add (((addCommGrpIsoAddEquiv
    (eqToIso (quotientNegativeTwistCechComplex_X I m n))).trans
      (addCommGrpProductAddEquivPi (quotientCechTermFamily I m n)))) x y

/-- The coordinate-cover section-representer chain of a projective quotient. -/
noncomputable abbrev quotientSectionRepresenterCechChain
    (I : HomogeneousIdeal AA) :
    ChainComplex (Proj (grading I)).Modules ℕ :=
  sectionRepresenterCechChain (Proj (grading I)).ringCatSheaf
    (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)

/-- Termwise Yoneda identification of the quotient section-representer Hom
complex with the dependent family of quotient-coordinate sections. -/
noncomputable def quotientSectionRepresenterCechHomEquivPi
    (I : HomogeneousIdeal AA) (m n : ℕ) :
    ((quotientSectionRepresenterCechChain I).X n ⟶
        sheafOfModules (grading I) m) ≃
      (∀ f : Fin (n + 1) → sigma, quotientCechTermFamily I m n f) :=
  (sectionRepresenterCechHomEquivPi (Proj (grading I)).ringCatSheaf
    (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
    (sheafOfModules (grading I) m) n).trans
      (Equiv.piCongrLeft
        (fun f : Fin (n + 1) → sigma => quotientCechTermFamily I m n f)
        (quotientIndexFunEquiv n))

/-- Termwise Yoneda identification of the quotient section-representer Hom
complex with the raw negative-twist Cech complex. -/
noncomputable def quotientSectionRepresenterCechHomEquiv
    (I : HomogeneousIdeal AA) (m n : ℕ) :
    ((quotientSectionRepresenterCechChain I).X n ⟶
        sheafOfModules (grading I) m) ≃
      (quotientNegativeTwistCechComplex I m).X n :=
  (quotientSectionRepresenterCechHomEquivPi I m n).trans
      (quotientNegativeTwistCechTermEquivPi I m n).symm

/-- Applying the raw-Cech product equivalence after the Yoneda equivalence
cancels the final inverse product equivalence. -/
lemma quotientNegativeTwistCechTermEquivPi_sectionRepresenterCechHomEquiv
    (I : HomogeneousIdeal AA) (m n : ℕ)
    (h : (quotientSectionRepresenterCechChain I).X n ⟶
      sheafOfModules (grading I) m) :
    quotientNegativeTwistCechTermEquivPi I m n
        (quotientSectionRepresenterCechHomEquiv I m n h) =
      quotientSectionRepresenterCechHomEquivPi I m n h := by
  exact (quotientNegativeTwistCechTermEquivPi I m n).apply_symm_apply
    (quotientSectionRepresenterCechHomEquivPi I m n h)

/-- Every term of the quotient coordinate-cover chain is Ext-acyclic in the
two degrees required for degree-two dimension shifting. -/
theorem quotient_sectionRepresenterCechChain_ext_one_and_two_subsingleton
    (I : HomogeneousIdeal AA) (m n : ℕ)
    [HasExt.{u} (Proj (grading I)).Modules] :
      Subsingleton
        (Ext.{u} (C := (Proj (grading I)).Modules)
          ((quotientSectionRepresenterCechChain I).X n)
          (sheafOfModules (grading I) m) 1) ∧
      Subsingleton
        (Ext.{u} (C := (Proj (grading I)).Modules)
          ((quotientSectionRepresenterCechChain I).X n)
          (sheafOfModules (grading I) m) 2) := by
  classical
  letI : Fintype sigma := Fintype.ofFinite sigma
  let V : ULift.{u} sigma → Scheme.Opens (Proj (grading I)) :=
    fun j => quotientCoordinateOpen I j.down
  let X : (Fin (n + 1) → ULift.{u} sigma) →
      (Proj (grading I)).Modules :=
    fun f => sectionRepresenter (Proj (grading I)).ringCatSheaf
      (∏ᶜ fun a => V (f a))
  have hlocal (f : Fin (n + 1) → ULift.{u} sigma) :
      Subsingleton (Ext.{u} (C := (Proj (grading I)).Modules)
        (X f) (sheafOfModules (grading I) m) 1) ∧
      Subsingleton (Ext.{u} (C := (Proj (grading I)).Modules)
        (X f) (sheafOfModules (grading I) m) 2) := by
    let g : Fin (n + 1) → sigma := fun a => (f a).down
    let W : Scheme.Opens (Proj (grading I)) :=
      ⨅ a, quotientCoordinateOpen I (g a)
    have hW :=
      quotientNegativeTwistCechInter_sectionRepresenter_ext_one_and_two_subsingleton
        I m n g
    have e : W = ∏ᶜ fun a => V (f a) :=
      (quotientCechProduct_eq_inf I n g).symm
    simpa only [X, ← e] using hW
  letI h₁ : ∀ f, Subsingleton
      (Ext.{u} (C := (Proj (grading I)).Modules)
        (X f) (sheafOfModules (grading I) m) 1) :=
    fun f => (hlocal f).1
  letI h₂ : ∀ f, Subsingleton
      (Ext.{u} (C := (Proj (grading I)).Modules)
        (X f) (sheafOfModules (grading I) m) 2) :=
    fun f => (hlocal f).2
  dsimp only [quotientSectionRepresenterCechChain]
  rw [sectionRepresenterCechChain_obj]
  change
    Subsingleton (Ext.{u} (C := (Proj (grading I)).Modules)
      (∐ X) (sheafOfModules (grading I) m) 1) ∧
    Subsingleton (Ext.{u} (C := (Proj (grading I)).Modules)
      (∐ X) (sheafOfModules (grading I) m) 2)
  exact ⟨
    ext_finite_coproduct_subsingleton X (sheafOfModules (grading I) m) 1,
    ext_finite_coproduct_subsingleton X (sheafOfModules (grading I) m) 2⟩

/-- The augmentation target of the quotient coordinate-cover chain. -/
noncomputable abbrev quotientSectionRepresenterCechTarget
    (I : HomogeneousIdeal AA) : (Proj (grading I)).Modules :=
  (sectionRepresenterCechAugmented (Proj (grading I)).ringCatSheaf
    (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
    (⊤ : Scheme.Opens (Proj (grading I))) isTerminalTop).right

/-- The quotient coordinate-cover augmentation. -/
noncomputable abbrev quotientSectionRepresenterCechAugmentation
    (I : HomogeneousIdeal AA) :
    (quotientSectionRepresenterCechChain I).X 0 ⟶
      quotientSectionRepresenterCechTarget I :=
  sectionRepresenterCechAugmentation (Proj (grading I)).ringCatSheaf
    (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
    (⊤ : Scheme.Opens (Proj (grading I))) isTerminalTop

/-- The lifted quotient coordinate family covers the projective quotient. -/
theorem quotientCoordinateOpenTop_coversTop
    (I : HomogeneousIdeal AA) :
    (Opens.grothendieckTopology (Proj (grading I))).CoversTop
      (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down) := by
  apply (Opens.coversTop_iff _ _).mpr
  apply TopologicalSpace.IsOpenCover.mk
  change (⨆ j : ULift.{u} sigma, quotientCoordinateOpen I j.down) = ⊤
  simpa [iSup_ulift] using quotientCoordinateOpen_iSup I

/-- Exactness at every positive degree of the quotient coordinate-cover
section-representer chain. -/
theorem quotientSectionRepresenterCechChain_exactAt_succ
    (I : HomogeneousIdeal AA) (n : ℕ) :
    (quotientSectionRepresenterCechChain I).ExactAt (n + 1) := by
  exact sectionRepresenterCechChain_exactAt_succ_of_coversTop
    (Proj (grading I)).ringCatSheaf
    (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
    (quotientCoordinateOpenTop_coversTop I) n

/-- Exactness at the augmentation spot, together with epimorphy of the
augmentation. -/
theorem quotientSectionRepresenterCech_augmentation_exact_and_epi
    (I : HomogeneousIdeal AA) :
    (sectionRepresenterCechAugmentationShortComplex
      (Proj (grading I)).ringCatSheaf
      (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
      (⊤ : Scheme.Opens (Proj (grading I))) isTerminalTop).Exact ∧
    Epi (quotientSectionRepresenterCechAugmentation I) := by
  exact sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    (Proj (grading I)).ringCatSheaf
    (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
    (quotientCoordinateOpenTop_coversTop I)
    (⊤ : Scheme.Opens (Proj (grading I))) isTerminalTop

theorem quotientSectionRepresenterCech_augmentation_exact
    (I : HomogeneousIdeal AA) :
    (ShortComplex.mk
      ((quotientSectionRepresenterCechChain I).d 1 0)
      (quotientSectionRepresenterCechAugmentation I)
      (sectionRepresenterCech_d_one_zero_comp_augmentation
        (Proj (grading I)).ringCatSheaf
        (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
        (⊤ : Scheme.Opens (Proj (grading I))) isTerminalTop)).Exact :=
  (quotientSectionRepresenterCech_augmentation_exact_and_epi I).1

theorem quotientSectionRepresenterCech_exact_one
    (I : HomogeneousIdeal AA) :
    (ShortComplex.mk
      ((quotientSectionRepresenterCechChain I).d 2 1)
      ((quotientSectionRepresenterCechChain I).d 1 0)
      ((quotientSectionRepresenterCechChain I).d_comp_d 2 1 0)).Exact := by
  have h := quotientSectionRepresenterCechChain_exactAt_succ I 0
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at h
  exact h

theorem quotientSectionRepresenterCech_exact_two
    (I : HomogeneousIdeal AA) :
    (ShortComplex.mk
      ((quotientSectionRepresenterCechChain I).d 3 2)
      ((quotientSectionRepresenterCechChain I).d 2 1)
      ((quotientSectionRepresenterCechChain I).d_comp_d 3 2 1)).Exact := by
  have h := quotientSectionRepresenterCechChain_exactAt_succ I 1
  rw [HomologicalComplex.exactAt_iff' _ 3 2 1 (by simp) (by simp)] at h
  exact h

/-- The augmentation target is canonically the structure sheaf. -/
noncomputable def quotientSectionRepresenterCechTargetIsoUnit
    (I : HomogeneousIdeal AA) :
    quotientSectionRepresenterCechTarget I ≅
      (show (Proj (grading I)).Modules from
        SheafOfModules.unit (Proj (grading I)).ringCatSheaf) :=
  (((FormalCoproduct.evalCompInclIsoId _ _).app
    (sectionRepresenterFunctor (Proj (grading I)).ringCatSheaf)).app ⊤) ≪≫
      sectionRepresenterTopIsoUnit (Proj (grading I))

/-- Degree-two Hom cocycles for the quotient coordinate-cover resolution. -/
abbrev QuotientCechDegreeTwoCocycle
    (I : HomogeneousIdeal AA) (m : ℕ) :=
  DegreeTwoCocycle
    ((quotientSectionRepresenterCechChain I).d 3 2)
    (Y := sheafOfModules (grading I) m)

/-- The canonical map from degree-two coordinate-cover Hom cocycles to
actual `Ext²` from the augmentation target. -/
def quotientCechDegreeTwoToAugmentedExt
    (I : HomogeneousIdeal AA) [HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) :
    QuotientCechDegreeTwoCocycle I m →
      Ext.{u} (quotientSectionRepresenterCechTarget I)
        (sheafOfModules (grading I) m) 2 := fun f => by
  letI : Epi (quotientSectionRepresenterCechAugmentation I) :=
    (quotientSectionRepresenterCech_augmentation_exact_and_epi I).2
  exact augmentedChainDegreeTwoToExt
    (quotientSectionRepresenterCechTarget I)
    ((quotientSectionRepresenterCechChain I).X 0)
    ((quotientSectionRepresenterCechChain I).X 1)
    ((quotientSectionRepresenterCechChain I).X 2)
    ((quotientSectionRepresenterCechChain I).X 3)
    (sheafOfModules (grading I) m)
    (quotientSectionRepresenterCechAugmentation I)
    ((quotientSectionRepresenterCechChain I).d 1 0)
    ((quotientSectionRepresenterCechChain I).d 2 1)
    ((quotientSectionRepresenterCechChain I).d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj (grading I)).ringCatSheaf
      (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
      (⊤ : Scheme.Opens (Proj (grading I))) isTerminalTop)
    ((quotientSectionRepresenterCechChain I).d_comp_d 2 1 0)
    ((quotientSectionRepresenterCechChain I).d_comp_d 3 2 1)
    (quotientSectionRepresenterCech_augmentation_exact I)
    (quotientSectionRepresenterCech_exact_one I)
    (quotientSectionRepresenterCech_exact_two I) f

@[simp]
theorem quotientCechDegreeTwoToAugmentedExt_zero
    (I : HomogeneousIdeal AA) [HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) :
    quotientCechDegreeTwoToAugmentedExt I m
      (0 : QuotientCechDegreeTwoCocycle I m) = 0 := by
  letI : Epi (quotientSectionRepresenterCechAugmentation I) :=
    (quotientSectionRepresenterCech_augmentation_exact_and_epi I).2
  unfold quotientCechDegreeTwoToAugmentedExt
  exact augmentedChainDegreeTwoToExt_zero
    (quotientSectionRepresenterCechTarget I)
    ((quotientSectionRepresenterCechChain I).X 0)
    ((quotientSectionRepresenterCechChain I).X 1)
    ((quotientSectionRepresenterCechChain I).X 2)
    ((quotientSectionRepresenterCechChain I).X 3)
    (sheafOfModules (grading I) m)
    (quotientSectionRepresenterCechAugmentation I)
    ((quotientSectionRepresenterCechChain I).d 1 0)
    ((quotientSectionRepresenterCechChain I).d 2 1)
    ((quotientSectionRepresenterCechChain I).d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj (grading I)).ringCatSheaf
      (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
      (⊤ : Scheme.Opens (Proj (grading I))) isTerminalTop)
    ((quotientSectionRepresenterCechChain I).d_comp_d 2 1 0)
    ((quotientSectionRepresenterCechChain I).d_comp_d 3 2 1)
    (quotientSectionRepresenterCech_augmentation_exact I)
    (quotientSectionRepresenterCech_exact_one I)
    (quotientSectionRepresenterCech_exact_two I)

theorem quotientCechDegreeTwoToAugmentedExt_add
    (I : HomogeneousIdeal AA) [HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) (f g : QuotientCechDegreeTwoCocycle I m) :
    quotientCechDegreeTwoToAugmentedExt I m (f + g) =
      quotientCechDegreeTwoToAugmentedExt I m f +
        quotientCechDegreeTwoToAugmentedExt I m g := by
  letI : Epi (quotientSectionRepresenterCechAugmentation I) :=
    (quotientSectionRepresenterCech_augmentation_exact_and_epi I).2
  unfold quotientCechDegreeTwoToAugmentedExt
  exact augmentedChainDegreeTwoToExt_add
    (quotientSectionRepresenterCechTarget I)
    ((quotientSectionRepresenterCechChain I).X 0)
    ((quotientSectionRepresenterCechChain I).X 1)
    ((quotientSectionRepresenterCechChain I).X 2)
    ((quotientSectionRepresenterCechChain I).X 3)
    (sheafOfModules (grading I) m)
    (quotientSectionRepresenterCechAugmentation I)
    ((quotientSectionRepresenterCechChain I).d 1 0)
    ((quotientSectionRepresenterCechChain I).d 2 1)
    ((quotientSectionRepresenterCechChain I).d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj (grading I)).ringCatSheaf
      (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
      (⊤ : Scheme.Opens (Proj (grading I))) isTerminalTop)
    ((quotientSectionRepresenterCechChain I).d_comp_d 2 1 0)
    ((quotientSectionRepresenterCechChain I).d_comp_d 3 2 1)
    (quotientSectionRepresenterCech_augmentation_exact I)
    (quotientSectionRepresenterCech_exact_one I)
    (quotientSectionRepresenterCech_exact_two I) f g

/-- The degree-two Cech-to-Ext comparison as an additive homomorphism. -/
def quotientCechDegreeTwoToAugmentedExtHom
    (I : HomogeneousIdeal AA) [HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) :
    QuotientCechDegreeTwoCocycle I m →+
      Ext.{u} (quotientSectionRepresenterCechTarget I)
        (sheafOfModules (grading I) m) 2 where
  toFun := quotientCechDegreeTwoToAugmentedExt I m
  map_zero' := quotientCechDegreeTwoToAugmentedExt_zero I m
  map_add' := quotientCechDegreeTwoToAugmentedExt_add I m

/-- Every actual `Ext²` class is represented by a coordinate-cover Hom
cocycle. -/
theorem quotientCechDegreeTwoToAugmentedExt_surjective
    (I : HomogeneousIdeal AA) [HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) :
    Function.Surjective (quotientCechDegreeTwoToAugmentedExt I m) := by
  letI : Epi (quotientSectionRepresenterCechAugmentation I) :=
    (quotientSectionRepresenterCech_augmentation_exact_and_epi I).2
  let h₀ := quotient_sectionRepresenterCechChain_ext_one_and_two_subsingleton
    I m 0
  let h₁ := quotient_sectionRepresenterCechChain_ext_one_and_two_subsingleton
    I m 1
  letI : Subsingleton (Ext.{u}
      ((quotientSectionRepresenterCechChain I).X 0)
      (sheafOfModules (grading I) m) 2) := h₀.2
  letI : Subsingleton (Ext.{u}
      ((quotientSectionRepresenterCechChain I).X 1)
      (sheafOfModules (grading I) m) 1) := h₁.1
  exact augmentedChainDegreeTwoToExt_surjective
    (quotientSectionRepresenterCechTarget I)
    ((quotientSectionRepresenterCechChain I).X 0)
    ((quotientSectionRepresenterCechChain I).X 1)
    ((quotientSectionRepresenterCechChain I).X 2)
    ((quotientSectionRepresenterCechChain I).X 3)
    (sheafOfModules (grading I) m)
    (quotientSectionRepresenterCechAugmentation I)
    ((quotientSectionRepresenterCechChain I).d 1 0)
    ((quotientSectionRepresenterCechChain I).d 2 1)
    ((quotientSectionRepresenterCechChain I).d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj (grading I)).ringCatSheaf
      (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
      (⊤ : Scheme.Opens (Proj (grading I))) isTerminalTop)
    ((quotientSectionRepresenterCechChain I).d_comp_d 2 1 0)
    ((quotientSectionRepresenterCechChain I).d_comp_d 3 2 1)
    (quotientSectionRepresenterCech_augmentation_exact I)
    (quotientSectionRepresenterCech_exact_one I)
    (quotientSectionRepresenterCech_exact_two I)

/-- A degree-two Hom cocycle dies in actual `Ext²` precisely when it is a
degree-one Hom boundary. -/
theorem quotientCechDegreeTwoToAugmentedExt_eq_zero_iff
    (I : HomogeneousIdeal AA) [HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) (f : QuotientCechDegreeTwoCocycle I m) :
    quotientCechDegreeTwoToAugmentedExt I m f = 0 ↔
      ∃ q : (quotientSectionRepresenterCechChain I).X 1 ⟶
          sheafOfModules (grading I) m,
        (quotientSectionRepresenterCechChain I).d 2 1 ≫ q = f.1 := by
  letI : Epi (quotientSectionRepresenterCechAugmentation I) :=
    (quotientSectionRepresenterCech_augmentation_exact_and_epi I).2
  let h₀ := quotient_sectionRepresenterCechChain_ext_one_and_two_subsingleton
    I m 0
  letI : Subsingleton (Ext.{u}
      ((quotientSectionRepresenterCechChain I).X 0)
      (sheafOfModules (grading I) m) 1) := h₀.1
  exact augmentedChainDegreeTwoToExt_eq_zero_iff
    (quotientSectionRepresenterCechTarget I)
    ((quotientSectionRepresenterCechChain I).X 0)
    ((quotientSectionRepresenterCechChain I).X 1)
    ((quotientSectionRepresenterCechChain I).X 2)
    ((quotientSectionRepresenterCechChain I).X 3)
    (sheafOfModules (grading I) m)
    (quotientSectionRepresenterCechAugmentation I)
    ((quotientSectionRepresenterCechChain I).d 1 0)
    ((quotientSectionRepresenterCechChain I).d 2 1)
    ((quotientSectionRepresenterCechChain I).d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj (grading I)).ringCatSheaf
      (fun j : ULift.{u} sigma => quotientCoordinateOpen I j.down)
      (⊤ : Scheme.Opens (Proj (grading I))) isTerminalTop)
    ((quotientSectionRepresenterCechChain I).d_comp_d 2 1 0)
    ((quotientSectionRepresenterCechChain I).d_comp_d 3 2 1)
    (quotientSectionRepresenterCech_augmentation_exact I)
    (quotientSectionRepresenterCech_exact_one I)
    (quotientSectionRepresenterCech_exact_two I) f

/-- The quotient of degree-two Cech cocycles by the actual boundary kernel
is actual `Ext²` from the augmentation target. -/
noncomputable def quotientCechDegreeTwoQuotientEquivAugmentedExt
    (I : HomogeneousIdeal AA) [HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) :
    QuotientCechDegreeTwoCocycle I m ⧸
        (quotientCechDegreeTwoToAugmentedExtHom I m).ker ≃+
      Ext.{u} (quotientSectionRepresenterCechTarget I)
        (sheafOfModules (grading I) m) 2 :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (quotientCechDegreeTwoToAugmentedExtHom I m)
    (quotientCechDegreeTwoToAugmentedExt_surjective I m)

/-- The same quotient computes actual second cohomology of the negative
twist on the projective quotient. -/
noncomputable def quotientCechDegreeTwoQuotientEquivCohomologyTwo
    (I : HomogeneousIdeal AA) [HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) :
    QuotientCechDegreeTwoCocycle I m ⧸
        (quotientCechDegreeTwoToAugmentedExtHom I m).ker ≃+
      schemeModuleCohomology (Proj (grading I))
        (sheafOfModules (grading I) m) 2 :=
  (quotientCechDegreeTwoQuotientEquivAugmentedExt I m).trans
    (extPrecompIsoOfIso (quotientSectionRepresenterCechTargetIsoUnit I))

end PfaffianDescent.ProjectiveNegativeTwist

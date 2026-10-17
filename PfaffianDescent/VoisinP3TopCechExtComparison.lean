import PfaffianDescent.CechExtDegreeThree
import PfaffianDescent.VoisinGlobalExtVanishing
import PfaffianDescent.VoisinP3TopCechSerreDuality
import PfaffianDescent.VoisinP3TopCechVanishing

/-!
# Comparison of the top Cech quotient with actual Ext on projective space

This specializes the abstract degree-three acyclic-resolution comparison to
the standard four-open cover of projective three-space.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial Opposite

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

variable (K : Type u) [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Every term of the section-representer Cech chain is Ext-acyclic through
degree three against a concrete negative twist. -/
theorem p3_sectionRepresenterCechChain_ext_one_two_three_subsingleton
    [HasExt.{u} (Proj PS).Modules] (m n : ℕ) :
      Subsingleton
        (Ext.{u} (C := (Proj PS).Modules)
          ((p3SectionRepresenterCechChain K).X n)
          (sheafOfModules PS m) 1) ∧
      Subsingleton
        (Ext.{u} (C := (Proj PS).Modules)
          ((p3SectionRepresenterCechChain K).X n)
          (sheafOfModules PS m) 2) ∧
      Subsingleton
        (Ext.{u} (C := (Proj PS).Modules)
          ((p3SectionRepresenterCechChain K).X n)
          (sheafOfModules PS m) 3) := by
  let V : ULift.{u} (Fin 4) → Scheme.Opens (Proj PS) :=
    fun i => p3StandardOpen (K := K) i.down
  let X : (Fin (n + 1) → ULift.{u} (Fin 4)) → (Proj PS).Modules :=
    fun f => sectionRepresenter (Proj PS).ringCatSheaf (∏ᶜ fun i => V (f i))
  have hlocal (f : Fin (n + 1) → ULift.{u} (Fin 4)) :
      Subsingleton (Ext.{u} (C := (Proj PS).Modules)
        (X f) (sheafOfModules PS m) 1) ∧
      Subsingleton (Ext.{u} (C := (Proj PS).Modules)
        (X f) (sheafOfModules PS m) 2) ∧
      Subsingleton (Ext.{u} (C := (Proj PS).Modules)
        (X f) (sheafOfModules PS m) 3) := by
    let g : Fin (n + 1) → Fin 4 := fun i => (f i).down
    let W : Scheme.Opens (Proj PS) :=
      ⨅ i, p3StandardOpen (K := K) (g i)
    have hW :=
      p3NegativeTwistCechInter_sectionRepresenter_ext_one_two_three_subsingleton
        K m n g
    have e : W = ∏ᶜ fun i => V (f i) :=
      (p3CechProduct_eq_inf K n g).symm
    simpa only [X, ← e] using hW
  letI h₁ : ∀ f, Subsingleton
      (Ext.{u} (C := (Proj PS).Modules)
        (X f) (sheafOfModules PS m) 1) :=
    fun f => (hlocal f).1
  letI h₂ : ∀ f, Subsingleton
      (Ext.{u} (C := (Proj PS).Modules)
        (X f) (sheafOfModules PS m) 2) :=
    fun f => (hlocal f).2.1
  letI h₃ : ∀ f, Subsingleton
      (Ext.{u} (C := (Proj PS).Modules)
        (X f) (sheafOfModules PS m) 3) :=
    fun f => (hlocal f).2.2
  dsimp only [p3SectionRepresenterCechChain]
  rw [sectionRepresenterCechChain_obj]
  change
    Subsingleton (Ext.{u} (C := (Proj PS).Modules)
      (∐ X) (sheafOfModules PS m) 1) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules)
      (∐ X) (sheafOfModules PS m) 2) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules)
      (∐ X) (sheafOfModules PS m) 3)
  exact ⟨
    ext_finite_coproduct_subsingleton X (sheafOfModules PS m) 1,
    ext_finite_coproduct_subsingleton X (sheafOfModules PS m) 2,
    ext_finite_coproduct_subsingleton X (sheafOfModules PS m) 3⟩

/-- The augmentation target of the standard-cover section-representer Cech
resolution on projective three-space. -/
noncomputable abbrev p3SectionRepresenterCechTarget :
    (Proj PS).Modules :=
  (sectionRepresenterCechAugmented (Proj PS).ringCatSheaf
    (fun i : ULift.{u} (Fin 4) => p3StandardOpen (K := K) i.down)
    (⊤ : Scheme.Opens (Proj PS)) isTerminalTop).right

/-- The augmentation of the standard-cover section-representer Cech
resolution. -/
noncomputable abbrev p3SectionRepresenterCechAugmentation :
    (p3SectionRepresenterCechChain K).X 0 ⟶
      p3SectionRepresenterCechTarget K :=
  sectionRepresenterCechAugmentation (Proj PS).ringCatSheaf
    (fun i : ULift.{u} (Fin 4) => p3StandardOpen (K := K) i.down)
    (⊤ : Scheme.Opens (Proj PS)) isTerminalTop

/-- The standard four opens cover projective three-space. -/
theorem p3StandardOpenTop_coversTop :
    (Opens.grothendieckTopology (Proj PS)).CoversTop
      (fun i : ULift.{u} (Fin 4) =>
        p3StandardOpen (K := K) i.down) := by
  apply (Opens.coversTop_iff _ _).mpr
  apply TopologicalSpace.IsOpenCover.mk
  change (⨆ i : ULift.{u} (Fin 4),
    p3StandardOpen (K := K) i.down) = ⊤
  simpa [iSup_ulift] using p3StandardOpen_iSup K

/-- Exactness of every positive spot of the standard-cover
section-representer Cech chain. -/
theorem p3SectionRepresenterCechChain_exactAt_succ (n : ℕ) :
    (p3SectionRepresenterCechChain K).ExactAt (n + 1) := by
  exact sectionRepresenterCechChain_exactAt_succ_of_coversTop
    (Proj PS).ringCatSheaf
    (fun i : ULift.{u} (Fin 4) =>
      p3StandardOpen (K := K) i.down)
    (p3StandardOpenTop_coversTop K) n

/-- The degree-zero augmentation spot is exact, and the augmentation is an
epimorphism. -/
theorem p3SectionRepresenterCech_augmentation_exact_and_epi :
    (sectionRepresenterCechAugmentationShortComplex
      (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 4) =>
        p3StandardOpen (K := K) i.down)
      (⊤ : Scheme.Opens (Proj PS)) isTerminalTop).Exact ∧
    Epi (p3SectionRepresenterCechAugmentation K) := by
  exact sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    (Proj PS).ringCatSheaf
    (fun i : ULift.{u} (Fin 4) =>
      p3StandardOpen (K := K) i.down)
    (p3StandardOpenTop_coversTop K)
    (⊤ : Scheme.Opens (Proj PS)) isTerminalTop

theorem p3SectionRepresenterCech_augmentation_exact :
    (ShortComplex.mk
      ((p3SectionRepresenterCechChain K).d 1 0)
      (p3SectionRepresenterCechAugmentation K)
      (sectionRepresenterCech_d_one_zero_comp_augmentation
        (Proj PS).ringCatSheaf
        (fun i : ULift.{u} (Fin 4) =>
          p3StandardOpen (K := K) i.down)
        (⊤ : Scheme.Opens (Proj PS)) isTerminalTop)).Exact :=
  (p3SectionRepresenterCech_augmentation_exact_and_epi K).1

theorem p3SectionRepresenterCech_exact_one :
    (ShortComplex.mk
      ((p3SectionRepresenterCechChain K).d 2 1)
      ((p3SectionRepresenterCechChain K).d 1 0)
      ((p3SectionRepresenterCechChain K).d_comp_d 2 1 0)).Exact := by
  have h := p3SectionRepresenterCechChain_exactAt_succ K 0
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at h
  exact h

theorem p3SectionRepresenterCech_exact_two :
    (ShortComplex.mk
      ((p3SectionRepresenterCechChain K).d 3 2)
      ((p3SectionRepresenterCechChain K).d 2 1)
      ((p3SectionRepresenterCechChain K).d_comp_d 3 2 1)).Exact := by
  have h := p3SectionRepresenterCechChain_exactAt_succ K 1
  rw [HomologicalComplex.exactAt_iff' _ 3 2 1 (by simp) (by simp)] at h
  exact h

theorem p3SectionRepresenterCech_exact_three :
    (ShortComplex.mk
      ((p3SectionRepresenterCechChain K).d 4 3)
      ((p3SectionRepresenterCechChain K).d 3 2)
      ((p3SectionRepresenterCechChain K).d_comp_d 4 3 2)).Exact := by
  have h := p3SectionRepresenterCechChain_exactAt_succ K 2
  rw [HomologicalComplex.exactAt_iff' _ 4 3 2 (by simp) (by simp)] at h
  exact h

/-- Raw degree-three Cech cocycles of a negative twist. -/
abbrev P3RawTopCocycle (m : ℕ) :=
  AddMonoidHom.ker
    ((p3NegativeTwistCechComplex (K := K) m).d 3 4).hom

/-- A raw top Cech cocycle transported to the Hom complex of the
section-representer resolution. -/
def p3SectionRepresenterTopCocycleOfRaw (m : ℕ)
    (w : P3RawTopCocycle K m) :
    DegreeThreeCocycle
      ((p3SectionRepresenterCechChain K).d 4 3)
      (Y := sheafOfModules PS m) := by
  let h := (p3SectionRepresenterCechHomEquiv K m 3).symm w.1
  refine ⟨h, ?_⟩
  change (p3SectionRepresenterCechChain K).d 4 3 ≫ h = 0
  apply (p3SectionRepresenterCechHomEquiv K m 4).injective
  rw [p3SectionRepresenterCechHomEquiv_d, Equiv.apply_symm_apply,
    w.2, p3SectionRepresenterCechHomEquiv_zero]

@[simp]
theorem p3SectionRepresenterTopCocycleOfRaw_zero (m : ℕ) :
    p3SectionRepresenterTopCocycleOfRaw K m
      (0 : P3RawTopCocycle K m) = 0 := by
  apply Subtype.ext
  change (p3SectionRepresenterCechHomEquiv K m 3).symm 0 = 0
  apply (p3SectionRepresenterCechHomEquiv K m 3).injective
  rw [Equiv.apply_symm_apply, p3SectionRepresenterCechHomEquiv_zero]

theorem p3SectionRepresenterTopCocycleOfRaw_add (m : ℕ)
    (x y : P3RawTopCocycle K m) :
    p3SectionRepresenterTopCocycleOfRaw K m (x + y) =
      p3SectionRepresenterTopCocycleOfRaw K m x +
        p3SectionRepresenterTopCocycleOfRaw K m y := by
  apply Subtype.ext
  change (p3SectionRepresenterCechHomEquiv K m 3).symm
      (x.1 + y.1) =
    (p3SectionRepresenterCechHomEquiv K m 3).symm x.1 +
      (p3SectionRepresenterCechHomEquiv K m 3).symm y.1
  apply (p3SectionRepresenterCechHomEquiv K m 3).injective
  rw [Equiv.apply_symm_apply,
    p3SectionRepresenterCechHomEquiv_add,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The canonical comparison from raw top Cech cocycles to actual
`Ext³` from the augmentation target. -/
def p3RawTopCocycleToAugmentedExt
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    P3RawTopCocycle K m →
      Ext.{u} (p3SectionRepresenterCechTarget K)
        (sheafOfModules PS m) 3 := fun w => by
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  exact augmentedChainDegreeThreeToExt
    (p3SectionRepresenterCechTarget K)
    ((p3SectionRepresenterCechChain K).X 0)
    ((p3SectionRepresenterCechChain K).X 1)
    ((p3SectionRepresenterCechChain K).X 2)
    ((p3SectionRepresenterCechChain K).X 3)
    ((p3SectionRepresenterCechChain K).X 4)
    (sheafOfModules PS m)
    (p3SectionRepresenterCechAugmentation K)
    ((p3SectionRepresenterCechChain K).d 1 0)
    ((p3SectionRepresenterCechChain K).d 2 1)
    ((p3SectionRepresenterCechChain K).d 3 2)
    ((p3SectionRepresenterCechChain K).d 4 3)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 4) =>
        p3StandardOpen (K := K) i.down)
      (⊤ : Scheme.Opens (Proj PS)) isTerminalTop)
    ((p3SectionRepresenterCechChain K).d_comp_d 2 1 0)
    ((p3SectionRepresenterCechChain K).d_comp_d 3 2 1)
    ((p3SectionRepresenterCechChain K).d_comp_d 4 3 2)
    (p3SectionRepresenterCech_augmentation_exact K)
    (p3SectionRepresenterCech_exact_one K)
    (p3SectionRepresenterCech_exact_two K)
    (p3SectionRepresenterCech_exact_three K)
    (p3SectionRepresenterTopCocycleOfRaw K m w)

@[simp]
theorem p3RawTopCocycleToAugmentedExt_zero
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    p3RawTopCocycleToAugmentedExt K m
      (0 : P3RawTopCocycle K m) = 0 := by
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  unfold p3RawTopCocycleToAugmentedExt
  rw [p3SectionRepresenterTopCocycleOfRaw_zero]
  exact augmentedChainDegreeThreeToExt_zero
    (p3SectionRepresenterCechTarget K)
    ((p3SectionRepresenterCechChain K).X 0)
    ((p3SectionRepresenterCechChain K).X 1)
    ((p3SectionRepresenterCechChain K).X 2)
    ((p3SectionRepresenterCechChain K).X 3)
    ((p3SectionRepresenterCechChain K).X 4)
    (sheafOfModules PS m)
    (p3SectionRepresenterCechAugmentation K)
    ((p3SectionRepresenterCechChain K).d 1 0)
    ((p3SectionRepresenterCechChain K).d 2 1)
    ((p3SectionRepresenterCechChain K).d 3 2)
    ((p3SectionRepresenterCechChain K).d 4 3)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 4) =>
        p3StandardOpen (K := K) i.down)
      (⊤ : Scheme.Opens (Proj PS)) isTerminalTop)
    ((p3SectionRepresenterCechChain K).d_comp_d 2 1 0)
    ((p3SectionRepresenterCechChain K).d_comp_d 3 2 1)
    ((p3SectionRepresenterCechChain K).d_comp_d 4 3 2)
    (p3SectionRepresenterCech_augmentation_exact K)
    (p3SectionRepresenterCech_exact_one K)
    (p3SectionRepresenterCech_exact_two K)
    (p3SectionRepresenterCech_exact_three K)

theorem p3RawTopCocycleToAugmentedExt_add
    [HasExt.{u} (Proj PS).Modules] (m : ℕ)
    (x y : P3RawTopCocycle K m) :
    p3RawTopCocycleToAugmentedExt K m (x + y) =
      p3RawTopCocycleToAugmentedExt K m x +
        p3RawTopCocycleToAugmentedExt K m y := by
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  unfold p3RawTopCocycleToAugmentedExt
  rw [p3SectionRepresenterTopCocycleOfRaw_add]
  exact augmentedChainDegreeThreeToExt_add
    (p3SectionRepresenterCechTarget K)
    ((p3SectionRepresenterCechChain K).X 0)
    ((p3SectionRepresenterCechChain K).X 1)
    ((p3SectionRepresenterCechChain K).X 2)
    ((p3SectionRepresenterCechChain K).X 3)
    ((p3SectionRepresenterCechChain K).X 4)
    (sheafOfModules PS m)
    (p3SectionRepresenterCechAugmentation K)
    ((p3SectionRepresenterCechChain K).d 1 0)
    ((p3SectionRepresenterCechChain K).d 2 1)
    ((p3SectionRepresenterCechChain K).d 3 2)
    ((p3SectionRepresenterCechChain K).d 4 3)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 4) =>
        p3StandardOpen (K := K) i.down)
      (⊤ : Scheme.Opens (Proj PS)) isTerminalTop)
    ((p3SectionRepresenterCechChain K).d_comp_d 2 1 0)
    ((p3SectionRepresenterCechChain K).d_comp_d 3 2 1)
    ((p3SectionRepresenterCechChain K).d_comp_d 4 3 2)
    (p3SectionRepresenterCech_augmentation_exact K)
    (p3SectionRepresenterCech_exact_one K)
    (p3SectionRepresenterCech_exact_two K)
    (p3SectionRepresenterCech_exact_three K)
    (p3SectionRepresenterTopCocycleOfRaw K m x)
    (p3SectionRepresenterTopCocycleOfRaw K m y)

/-- The comparison from raw top Cech cocycles to actual `Ext³`, as an
additive homomorphism. -/
def p3RawTopCocycleToAugmentedExtHom
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    P3RawTopCocycle K m →+
      Ext.{u} (p3SectionRepresenterCechTarget K)
        (sheafOfModules PS m) 3 where
  toFun := p3RawTopCocycleToAugmentedExt K m
  map_zero' := p3RawTopCocycleToAugmentedExt_zero K m
  map_add' := p3RawTopCocycleToAugmentedExt_add K m

/-- Every actual `Ext³` class from the augmentation target is represented
by a raw top Cech cocycle. -/
theorem p3RawTopCocycleToAugmentedExt_surjective
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Function.Surjective (p3RawTopCocycleToAugmentedExt K m) := by
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  let h₀ :=
    p3_sectionRepresenterCechChain_ext_one_two_three_subsingleton K m 0
  let h₁ :=
    p3_sectionRepresenterCechChain_ext_one_two_three_subsingleton K m 1
  let h₂ :=
    p3_sectionRepresenterCechChain_ext_one_two_three_subsingleton K m 2
  letI : Subsingleton (Ext.{u}
      ((p3SectionRepresenterCechChain K).X 0)
      (sheafOfModules PS m) 3) := h₀.2.2
  letI : Subsingleton (Ext.{u}
      ((p3SectionRepresenterCechChain K).X 1)
      (sheafOfModules PS m) 2) := h₁.2.1
  letI : Subsingleton (Ext.{u}
      ((p3SectionRepresenterCechChain K).X 2)
      (sheafOfModules PS m) 1) := h₂.1
  have hs := augmentedChainDegreeThreeToExt_surjective
    (p3SectionRepresenterCechTarget K)
    ((p3SectionRepresenterCechChain K).X 0)
    ((p3SectionRepresenterCechChain K).X 1)
    ((p3SectionRepresenterCechChain K).X 2)
    ((p3SectionRepresenterCechChain K).X 3)
    ((p3SectionRepresenterCechChain K).X 4)
    (sheafOfModules PS m)
    (p3SectionRepresenterCechAugmentation K)
    ((p3SectionRepresenterCechChain K).d 1 0)
    ((p3SectionRepresenterCechChain K).d 2 1)
    ((p3SectionRepresenterCechChain K).d 3 2)
    ((p3SectionRepresenterCechChain K).d 4 3)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 4) =>
        p3StandardOpen (K := K) i.down)
      (⊤ : Scheme.Opens (Proj PS)) isTerminalTop)
    ((p3SectionRepresenterCechChain K).d_comp_d 2 1 0)
    ((p3SectionRepresenterCechChain K).d_comp_d 3 2 1)
    ((p3SectionRepresenterCechChain K).d_comp_d 4 3 2)
    (p3SectionRepresenterCech_augmentation_exact K)
    (p3SectionRepresenterCech_exact_one K)
    (p3SectionRepresenterCech_exact_two K)
    (p3SectionRepresenterCech_exact_three K)
  intro z
  obtain ⟨f, hf⟩ := hs z
  let w : P3RawTopCocycle K m :=
    ⟨p3SectionRepresenterCechHomEquiv K m 3 f.1, by
      change (p3NegativeTwistCechComplex (K := K) m).d 3 4
        (p3SectionRepresenterCechHomEquiv K m 3 f.1) = 0
      have hfzero :
          (p3SectionRepresenterCechChain K).d 4 3 ≫ f.1 = 0 := f.2
      rw [← p3SectionRepresenterCechHomEquiv_d, hfzero,
        p3SectionRepresenterCechHomEquiv_zero]⟩
  refine ⟨w, ?_⟩
  have hw : p3SectionRepresenterTopCocycleOfRaw K m w = f := by
    apply Subtype.ext
    change (p3SectionRepresenterCechHomEquiv K m 3).symm
      (p3SectionRepresenterCechHomEquiv K m 3 f.1) = f.1
    exact (p3SectionRepresenterCechHomEquiv K m 3).symm_apply_apply f.1
  change augmentedChainDegreeThreeToExt
      (p3SectionRepresenterCechTarget K)
      ((p3SectionRepresenterCechChain K).X 0)
      ((p3SectionRepresenterCechChain K).X 1)
      ((p3SectionRepresenterCechChain K).X 2)
      ((p3SectionRepresenterCechChain K).X 3)
      ((p3SectionRepresenterCechChain K).X 4)
      (sheafOfModules PS m)
      (p3SectionRepresenterCechAugmentation K)
      ((p3SectionRepresenterCechChain K).d 1 0)
      ((p3SectionRepresenterCechChain K).d 2 1)
      ((p3SectionRepresenterCechChain K).d 3 2)
      ((p3SectionRepresenterCechChain K).d 4 3)
      _ _ _ _ _ _ _ _
      (p3SectionRepresenterTopCocycleOfRaw K m w) = z
  rw [hw]
  exact hf

/-- A raw top cocycle maps to zero in actual `Ext³` exactly when it is a
raw Cech boundary. -/
theorem p3RawTopCocycleToAugmentedExt_eq_zero_iff
    [HasExt.{u} (Proj PS).Modules] (m : ℕ)
    (w : P3RawTopCocycle K m) :
    p3RawTopCocycleToAugmentedExt K m w = 0 ↔
      ∃ y : (p3NegativeTwistCechComplex (K := K) m).X 2,
        (p3NegativeTwistCechComplex (K := K) m).d 2 3 y = w.1 := by
  letI : Epi (p3SectionRepresenterCechAugmentation K) :=
    (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  let h₀ :=
    p3_sectionRepresenterCechChain_ext_one_two_three_subsingleton K m 0
  let h₁ :=
    p3_sectionRepresenterCechChain_ext_one_two_three_subsingleton K m 1
  letI : Subsingleton (Ext.{u}
      ((p3SectionRepresenterCechChain K).X 0)
      (sheafOfModules PS m) 2) := h₀.2.1
  letI : Subsingleton (Ext.{u}
      ((p3SectionRepresenterCechChain K).X 1)
      (sheafOfModules PS m) 1) := h₁.1
  let f := p3SectionRepresenterTopCocycleOfRaw K m w
  have hc := augmentedChainDegreeThreeToExt_eq_zero_iff
    (p3SectionRepresenterCechTarget K)
    ((p3SectionRepresenterCechChain K).X 0)
    ((p3SectionRepresenterCechChain K).X 1)
    ((p3SectionRepresenterCechChain K).X 2)
    ((p3SectionRepresenterCechChain K).X 3)
    ((p3SectionRepresenterCechChain K).X 4)
    (sheafOfModules PS m)
    (p3SectionRepresenterCechAugmentation K)
    ((p3SectionRepresenterCechChain K).d 1 0)
    ((p3SectionRepresenterCechChain K).d 2 1)
    ((p3SectionRepresenterCechChain K).d 3 2)
    ((p3SectionRepresenterCechChain K).d 4 3)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj PS).ringCatSheaf
      (fun i : ULift.{u} (Fin 4) =>
        p3StandardOpen (K := K) i.down)
      (⊤ : Scheme.Opens (Proj PS)) isTerminalTop)
    ((p3SectionRepresenterCechChain K).d_comp_d 2 1 0)
    ((p3SectionRepresenterCechChain K).d_comp_d 3 2 1)
    ((p3SectionRepresenterCechChain K).d_comp_d 4 3 2)
    (p3SectionRepresenterCech_augmentation_exact K)
    (p3SectionRepresenterCech_exact_one K)
    (p3SectionRepresenterCech_exact_two K)
    (p3SectionRepresenterCech_exact_three K)
    f
  constructor
  · intro hw0
    obtain ⟨q, hq⟩ := hc.mp (by
      simpa only [p3RawTopCocycleToAugmentedExt, f] using hw0)
    refine ⟨p3SectionRepresenterCechHomEquiv K m 2 q, ?_⟩
    rw [← p3SectionRepresenterCechHomEquiv_d, hq]
    change (p3SectionRepresenterCechHomEquiv K m 3)
      ((p3SectionRepresenterCechHomEquiv K m 3).symm w.1) = w.1
    exact (p3SectionRepresenterCechHomEquiv K m 3).apply_symm_apply w.1
  · rintro ⟨y, hy⟩
    apply hc.mpr
    let q := (p3SectionRepresenterCechHomEquiv K m 2).symm y
    refine ⟨q, ?_⟩
    apply (p3SectionRepresenterCechHomEquiv K m 3).injective
    rw [p3SectionRepresenterCechHomEquiv_d, Equiv.apply_symm_apply, hy]
    change w.1 = (p3SectionRepresenterCechHomEquiv K m 3)
      ((p3SectionRepresenterCechHomEquiv K m 3).symm w.1)
    exact ((p3SectionRepresenterCechHomEquiv K m 3).apply_symm_apply w.1).symm

/-- For `O(-6)`, the kernel of the Cech-to-`Ext³` comparison is exactly
the kernel detected by the ten quadratic residue coordinates. -/
theorem p3NegativeSixRawTopCocycleToAugmentedExt_ker_eq_residue_ker
    [HasExt.{u} (Proj PS).Modules] :
    (p3RawTopCocycleToAugmentedExtHom K 6).ker =
      (p3NegativeSixTopResidueCoordinates K).ker := by
  ext w
  let w' : p3NegativeSixTopCocycles K := ⟨w.1, w.2⟩
  change p3RawTopCocycleToAugmentedExt K 6 w = 0 ↔
    w' ∈ (p3NegativeSixTopResidueCoordinates K).ker
  rw [p3RawTopCocycleToAugmentedExt_eq_zero_iff,
    mem_p3NegativeSixTopResidueCoordinates_ker_iff_boundary]

/-- The explicit top Cech quotient of `O(-6)` is actual `Ext³` from the
augmentation target of the section-representer resolution. -/
noncomputable def p3NegativeSixTopCechQuotientEquivAugmentedExt
    [HasExt.{u} (Proj PS).Modules] :
    p3NegativeSixTopCocycles K ⧸
        (p3NegativeSixTopResidueCoordinates K).ker ≃+
      Ext.{u} (p3SectionRepresenterCechTarget K)
        (sheafOfModules PS 6) 3 := by
  rw [← p3NegativeSixRawTopCocycleToAugmentedExt_ker_eq_residue_ker K]
  exact QuotientAddGroup.quotientKerEquivOfSurjective
    (p3RawTopCocycleToAugmentedExtHom K 6)
    (p3RawTopCocycleToAugmentedExt_surjective K 6)

/-- The augmentation target is the section representer of the terminal
open of projective three-space. -/
noncomputable def p3SectionRepresenterCechTargetIsoTop :
    p3SectionRepresenterCechTarget K ≅
      sectionRepresenter (Proj PS).ringCatSheaf
        (⊤ : Scheme.Opens (Proj PS)) :=
  ((FormalCoproduct.evalCompInclIsoId _ _).app
    (sectionRepresenterFunctor (Proj PS).ringCatSheaf)).app ⊤

/-- The augmentation target is canonically isomorphic to the unit
`O_{P³}` module representing global sections. -/
noncomputable def p3SectionRepresenterCechTargetIsoUnit :
    p3SectionRepresenterCechTarget K ≅
      (show (Proj PS).Modules from
        SheafOfModules.unit (Proj PS).ringCatSheaf) :=
  p3SectionRepresenterCechTargetIsoTop K ≪≫
    sectionRepresenterTopIsoUnit (Proj PS)

/-- The explicit top Cech quotient computes actual third cohomology of
`O(-6)` on projective three-space. -/
noncomputable def p3NegativeSixTopCechQuotientEquivCohomologyThree
    [HasExt.{u} (Proj PS).Modules] :
    p3NegativeSixTopCocycles K ⧸
        (p3NegativeSixTopResidueCoordinates K).ker ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 6) 3 :=
  (p3NegativeSixTopCechQuotientEquivAugmentedExt K).trans
    (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K))

/-- The third cohomology of `O(-3)` on projective three-space vanishes. -/
theorem p3NegativeThree_cohomology_three_subsingleton
    [HasExt.{u} (Proj PS).Modules] :
    Subsingleton
      (schemeModuleCohomology (Proj PS) (sheafOfModules PS 3) 3) := by
  have hAug : Subsingleton
      (Ext.{u} (p3SectionRepresenterCechTarget K)
        (sheafOfModules PS 3) 3) := by
    apply subsingleton_of_forall_eq 0
    intro z
    obtain ⟨w, rfl⟩ := p3RawTopCocycleToAugmentedExt_surjective K 3 z
    apply (p3RawTopCocycleToAugmentedExt_eq_zero_iff K 3 w).2
    exact p3NegativeThreeRawCocycle_is_boundary K w.1 w.2
  exact (extPrecompIsoOfIso
    (p3SectionRepresenterCechTargetIsoUnit K)).toEquiv.subsingleton_congr.mp hAug

/-- Concrete Serre duality for actual `Ext³` from the standard-cover
augmentation target. -/
noncomputable def p3NegativeSixAugmentedExtDualQuadraticEquiv
    [HasExt.{u} (Proj PS).Modules] :
    Ext.{u} (p3SectionRepresenterCechTarget K)
        (sheafOfModules PS 6) 3 ≃+
      Module.Dual K (homogeneousSubmodule (Fin 4) K 2) :=
  (p3NegativeSixTopCechQuotientEquivAugmentedExt K).symm.trans
    (p3NegativeSixTopCechCohomologyDualQuadraticEquiv K)

/-- Concrete Serre duality for actual third cohomology of `O(-6)` on
projective three-space. -/
noncomputable def p3NegativeSixCohomologyThreeDualQuadraticEquiv
    [HasExt.{u} (Proj PS).Modules] :
    schemeModuleCohomology (Proj PS) (sheafOfModules PS 6) 3 ≃+
      Module.Dual K (homogeneousSubmodule (Fin 4) K 2) :=
  (extPrecompIsoOfIso
      (p3SectionRepresenterCechTargetIsoUnit K)).symm.trans
    (p3NegativeSixAugmentedExtDualQuadraticEquiv K)

end PfaffianDescent.ProjectiveNegativeTwist

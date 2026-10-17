import PfaffianDescent.ExtAcyclicResolutionDegreeTwo
import PfaffianDescent.CechExtDegreeThree

/-!
# Degree-two Ext from an augmented Cech resolution

This file turns the first two exact spots of an augmented chain into the two
short exact sequences used for degree-two dimension shifting.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PfaffianDescent

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/- The two-step resolution extracted from the first two exact spots of an
augmented chain. -/
def twoStepResolutionOfAugmentedChain
    (P C₀ C₁ C₂ : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    [Epi epsilon] :
    TwoStepResolution A where
  P := P
  C₀ := C₀
  C₁ := C₁
  K₀ := Abelian.image d₁
  K₁ := Abelian.coimage d₂
  i₀ := Abelian.image.ι d₁
  p₀ := epsilon
  zero₀ := Abelian.image_ι_comp_eq_zero h₁₀
  i₁ := Abelian.factorThruCoimage d₂
  p₁ := Abelian.factorThruImage d₁
  zero₁ := by
    apply (cancel_mono (Abelian.image.ι d₁)).1
    rw [Category.assoc, Abelian.image.fac, zero_comp]
    apply (cancel_epi (Abelian.coimage.π d₂)).1
    simpa only [← Category.assoc, Abelian.coimage.fac, comp_zero] using h₂₁
  exact₀ := by
    have hExact :
        (ShortComplex.mk (Abelian.image.ι d₁) epsilon
          (Abelian.image_ι_comp_eq_zero h₁₀)).Exact :=
      ((ShortComplex.mk d₁ epsilon h₁₀).exact_iff_exact_image_ι).mp hexact₀
    exact ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  exact₁ := by
    let T : ShortComplex A :=
      ShortComplex.mk (Abelian.factorThruCoimage d₂) d₁ (by
        apply (cancel_epi (Abelian.coimage.π d₂)).1
        simpa only [← Category.assoc, Abelian.coimage.fac, comp_zero] using h₂₁)
    have hT : T.Exact := by
      let S : ShortComplex A := ShortComplex.mk d₂ d₁ h₂₁
      let phi : S ⟶ T :=
        { τ₁ := Abelian.coimage.π d₂
          τ₂ := 𝟙 _
          τ₃ := 𝟙 _ }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono phi).mp hexact₁
    let S : ShortComplex A :=
      ShortComplex.mk (Abelian.factorThruCoimage d₂)
        (Abelian.factorThruImage d₁) (by
          apply (cancel_mono (Abelian.image.ι d₁)).1
          simpa only [Category.assoc, Abelian.image.fac, zero_comp] using T.zero)
    have hS : S.Exact := by
      let phi : S ⟶ T :=
        { τ₁ := 𝟙 _
          τ₂ := 𝟙 _
          τ₃ := Abelian.image.ι d₁ }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono phi).mpr hT
    exact ShortComplex.ShortExact.mk' hS inferInstance inferInstance

/- Degree-two cocycles in the Hom complex of a chain. -/
def DegreeTwoCocycle {C₂ C₃ Y : A} (d₃ : C₃ ⟶ C₂) :=
  (homPrecompAddMonoidHom (Y := Y) d₃).ker

/- At an exact spot, a degree-two cocycle descends to the coimage of the
preceding differential. -/
def degreeTwoCocycleDesc
    {C₁ C₂ C₃ Y : A} (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (f : DegreeTwoCocycle d₃ (Y := Y)) :
    Abelian.coimage d₂ ⟶ Y :=
  hexact₂.isColimitCoimage.desc (CokernelCofork.ofπ f.1 f.2)

@[reassoc]
theorem coimage_π_comp_degreeTwoCocycleDesc
    {C₁ C₂ C₃ Y : A} (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (f : DegreeTwoCocycle d₃ (Y := Y)) :
    Abelian.coimage.π d₂ ≫
      degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f = f.1 := by
  simpa [degreeTwoCocycleDesc] using
    hexact₂.isColimitCoimage.fac (CokernelCofork.ofπ f.1 f.2)
      WalkingParallelPair.one

@[simp]
theorem degreeTwoCocycleDesc_zero
    {C₁ C₂ C₃ Y : A} (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact) :
    degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂
      (0 : DegreeTwoCocycle d₃ (Y := Y)) = 0 := by
  apply (cancel_epi (Abelian.coimage.π d₂)).1
  rw [coimage_π_comp_degreeTwoCocycleDesc, comp_zero]
  rfl

theorem degreeTwoCocycleDesc_add
    {C₁ C₂ C₃ Y : A} (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (f g : DegreeTwoCocycle d₃ (Y := Y)) :
    degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ (f + g) =
      degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f +
        degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ g := by
  apply (cancel_epi (Abelian.coimage.π d₂)).1
  rw [coimage_π_comp_degreeTwoCocycleDesc, Preadditive.comp_add,
    coimage_π_comp_degreeTwoCocycleDesc,
    coimage_π_comp_degreeTwoCocycleDesc]
  rfl

/- The canonical map from degree-two Hom cocycles to `Ext²`. -/
def augmentedChainDegreeTwoToExt
    (P C₀ C₁ C₂ C₃ Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    [Epi epsilon] (f : DegreeTwoCocycle d₃ (Y := Y)) :
    Ext P Y 2 :=
  let R := twoStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁
  R.connecting Y (degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f)

@[simp]
theorem augmentedChainDegreeTwoToExt_zero
    (P C₀ C₁ C₂ C₃ Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    [Epi epsilon] :
    augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y
      epsilon d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ 0 = 0 := by
  let R := twoStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁
  change R.connecting Y (degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ 0) = 0
  rw [degreeTwoCocycleDesc_zero]
  exact R.connecting_zero Y

theorem augmentedChainDegreeTwoToExt_add
    (P C₀ C₁ C₂ C₃ Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    [Epi epsilon] (f g : DegreeTwoCocycle d₃ (Y := Y)) :
    augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y
        epsilon d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ (f + g) =
      augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y
          epsilon d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ f +
        augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y
          epsilon d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ g := by
  let R := twoStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁
  change R.connecting Y
      (degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ (f + g)) =
    R.connecting Y (degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f) +
      R.connecting Y (degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ g)
  rw [degreeTwoCocycleDesc_add]
  exact R.connecting_add Y _ _

/- Under local acyclicity, every `Ext²` class is represented by a
degree-two Hom cocycle. -/
theorem augmentedChainDegreeTwoToExt_surjective
    (P C₀ C₁ C₂ C₃ Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    [Epi epsilon]
    [Subsingleton (Ext C₀ Y 2)]
    [Subsingleton (Ext C₁ Y 1)] :
    Function.Surjective
      (augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y
        epsilon d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂) := by
  let R := twoStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁
  letI : Subsingleton (Ext R.C₀ Y 2) := by
    change Subsingleton (Ext C₀ Y 2)
    infer_instance
  letI : Subsingleton (Ext R.C₁ Y 1) := by
    change Subsingleton (Ext C₁ Y 1)
    infer_instance
  intro z
  obtain ⟨q, hq⟩ := R.connecting_surjective Y z
  change Abelian.coimage d₂ ⟶ Y at q
  let f : DegreeTwoCocycle d₃ (Y := Y) :=
    ⟨Abelian.coimage.π d₂ ≫ q, by
      change d₃ ≫ (Abelian.coimage.π d₂ ≫ q) = 0
      rw [← Category.assoc, Abelian.comp_coimage_π_eq_zero h₃₂, zero_comp]⟩
  refine ⟨f, ?_⟩
  change R.connecting Y (degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f) = z
  rw [show degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f = q by
    apply (cancel_epi (Abelian.coimage.π d₂)).1
    rw [coimage_π_comp_degreeTwoCocycleDesc]]
  exact hq

/- A degree-two cocycle maps to zero in `Ext²` exactly when it is a
degree-one boundary. -/
theorem augmentedChainDegreeTwoToExt_eq_zero_iff
    (P C₀ C₁ C₂ C₃ Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    [Epi epsilon]
    [Subsingleton (Ext C₀ Y 1)]
    (f : DegreeTwoCocycle d₃ (Y := Y)) :
    augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y
      epsilon d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ f = 0 ↔
      ∃ q : C₁ ⟶ Y, d₂ ≫ q = f.1 := by
  let R := twoStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁
  letI : Subsingleton (Ext R.C₀ Y 1) := by
    change Subsingleton (Ext C₀ Y 1)
    infer_instance
  have hc := R.connecting_eq_zero_iff Y
    (show R.K₁ ⟶ Y from degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f)
  constructor
  · intro h
    obtain ⟨q, hq⟩ := hc.mp h
    change C₁ ⟶ Y at q
    change Abelian.factorThruCoimage d₂ ≫ q =
      degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f at hq
    refine ⟨q, ?_⟩
    rw [← Abelian.coimage.fac d₂, Category.assoc, hq,
      coimage_π_comp_degreeTwoCocycleDesc]
  · rintro ⟨q, hq⟩
    apply hc.mpr
    refine ⟨q, ?_⟩
    change Abelian.factorThruCoimage d₂ ≫ q =
      degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f
    apply (cancel_epi (Abelian.coimage.π d₂)).1
    rw [← Category.assoc, Abelian.coimage.fac, hq,
      coimage_π_comp_degreeTwoCocycleDesc]

end PfaffianDescent

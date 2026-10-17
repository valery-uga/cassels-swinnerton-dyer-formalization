import PfaffianDescent.CechExtVanishingLowDegree
import PfaffianDescent.ExtAcyclicResolutionDegreeThree

/-!
# Degree-three Ext from an augmented Cech resolution

This file turns the first three exact spots of an augmented chain into the
three short exact sequences used for dimension shifting.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PfaffianDescent

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- The three-step resolution canonically extracted from the first three
exact spots of an augmented chain. -/
def threeStepResolutionOfAugmentedChain
    (P C₀ C₁ C₂ C₃ : A)
    (ε : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂)
    (h₁₀ : d₁ ≫ ε = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₀ : (ShortComplex.mk d₁ ε h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    [Epi ε] :
    ThreeStepResolution A where
  P := P
  C₀ := C₀
  C₁ := C₁
  C₂ := C₂
  K₀ := Abelian.image d₁
  K₁ := Abelian.coimage d₂
  K₂ := Abelian.coimage d₃
  i₀ := Abelian.image.ι d₁
  p₀ := ε
  zero₀ := Abelian.image_ι_comp_eq_zero h₁₀
  i₁ := Abelian.factorThruCoimage d₂
  p₁ := Abelian.factorThruImage d₁
  zero₁ := by
    apply (cancel_mono (Abelian.image.ι d₁)).1
    rw [Category.assoc, Abelian.image.fac, zero_comp]
    apply (cancel_epi (Abelian.coimage.π d₂)).1
    simpa only [← Category.assoc, Abelian.coimage.fac, comp_zero] using h₂₁
  i₂ := Abelian.factorThruCoimage d₃
  p₂ := Abelian.coimage.π d₂
  zero₂ := by
    apply (cancel_mono (Abelian.factorThruCoimage d₂)).1
    rw [Category.assoc, Abelian.coimage.fac, zero_comp]
    apply (cancel_epi (Abelian.coimage.π d₃)).1
    simpa only [← Category.assoc, Abelian.coimage.fac, comp_zero] using h₃₂
  exact₀ := by
    have hExact :
        (ShortComplex.mk (Abelian.image.ι d₁) ε
          (Abelian.image_ι_comp_eq_zero h₁₀)).Exact :=
      ((ShortComplex.mk d₁ ε h₁₀).exact_iff_exact_image_ι).mp hexact₀
    exact ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  exact₁ := by
    let T : ShortComplex A :=
      ShortComplex.mk (Abelian.factorThruCoimage d₂) d₁ (by
        apply (cancel_epi (Abelian.coimage.π d₂)).1
        simpa only [← Category.assoc, Abelian.coimage.fac, comp_zero] using h₂₁)
    have hT : T.Exact := by
      let S : ShortComplex A := ShortComplex.mk d₂ d₁ h₂₁
      let φ : S ⟶ T :=
        { τ₁ := Abelian.coimage.π d₂
          τ₂ := 𝟙 _
          τ₃ := 𝟙 _ }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hexact₁
    let S : ShortComplex A :=
      ShortComplex.mk (Abelian.factorThruCoimage d₂)
        (Abelian.factorThruImage d₁) (by
          apply (cancel_mono (Abelian.image.ι d₁)).1
          simpa only [Category.assoc, Abelian.image.fac, zero_comp] using T.zero)
    have hS : S.Exact := by
      let φ : S ⟶ T :=
        { τ₁ := 𝟙 _
          τ₂ := 𝟙 _
          τ₃ := Abelian.image.ι d₁ }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hT
    exact ShortComplex.ShortExact.mk' hS inferInstance inferInstance
  exact₂ := by
    let T : ShortComplex A :=
      ShortComplex.mk (Abelian.factorThruCoimage d₃) d₂ (by
        apply (cancel_epi (Abelian.coimage.π d₃)).1
        simpa only [← Category.assoc, Abelian.coimage.fac, comp_zero] using h₃₂)
    have hT : T.Exact := by
      let Q : ShortComplex A := ShortComplex.mk d₃ d₂ h₃₂
      let φ : Q ⟶ T :=
        { τ₁ := Abelian.coimage.π d₃
          τ₂ := 𝟙 _
          τ₃ := 𝟙 _ }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hexact₂
    let S : ShortComplex A :=
      ShortComplex.mk (Abelian.factorThruCoimage d₃)
        (Abelian.coimage.π d₂) (by
          apply (cancel_mono (Abelian.factorThruCoimage d₂)).1
          rw [Category.assoc, Abelian.coimage.fac, zero_comp]
          apply (cancel_epi (Abelian.coimage.π d₃)).1
          simpa only [← Category.assoc, Abelian.coimage.fac, comp_zero] using h₃₂)
    have hS : S.Exact := by
      let φ : S ⟶ T :=
        { τ₁ := 𝟙 _
          τ₂ := 𝟙 _
          τ₃ := Abelian.factorThruCoimage d₂ }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hT
    exact ShortComplex.ShortExact.mk' hS inferInstance inferInstance

/-- Precomposition by a chain differential, as an additive homomorphism. -/
def homPrecompAddMonoidHom {C₃ C₄ Y : A} (d₄ : C₄ ⟶ C₃) :
    (C₃ ⟶ Y) →+ (C₄ ⟶ Y) where
  toFun f := d₄ ≫ f
  map_zero' := by simp
  map_add' f g := by simp

/-- Degree-three cocycles in the Hom complex of a chain. -/
def DegreeThreeCocycle {C₃ C₄ Y : A} (d₄ : C₄ ⟶ C₃) :=
  (homPrecompAddMonoidHom (Y := Y) d₄).ker

/-- An exact spot `C₄ ⟶ C₃ ⟶ C₂` makes the coimage of the second
differential the cokernel of the first, so every degree-three cocycle
descends canonically to that coimage. -/
def degreeThreeCocycleDesc
    {C₂ C₃ C₄ Y : A} (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    (f : DegreeThreeCocycle d₄ (Y := Y)) :
    Abelian.coimage d₃ ⟶ Y :=
  hexact₃.isColimitCoimage.desc (CokernelCofork.ofπ f.1 f.2)

@[reassoc]
theorem coimage_π_comp_degreeThreeCocycleDesc
    {C₂ C₃ C₄ Y : A} (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    (f : DegreeThreeCocycle d₄ (Y := Y)) :
    Abelian.coimage.π d₃ ≫
      degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f = f.1 := by
  simpa [degreeThreeCocycleDesc] using
    hexact₃.isColimitCoimage.fac (CokernelCofork.ofπ f.1 f.2)
      WalkingParallelPair.one

@[simp]
theorem degreeThreeCocycleDesc_zero
    {C₂ C₃ C₄ Y : A} (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact) :
    degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃
      (0 : DegreeThreeCocycle d₄ (Y := Y)) = 0 := by
  apply (cancel_epi (Abelian.coimage.π d₃)).1
  rw [coimage_π_comp_degreeThreeCocycleDesc, comp_zero]
  rfl

theorem degreeThreeCocycleDesc_add
    {C₂ C₃ C₄ Y : A} (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    (f g : DegreeThreeCocycle d₄ (Y := Y)) :
    degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ (f + g) =
      degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f +
        degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ g := by
  apply (cancel_epi (Abelian.coimage.π d₃)).1
  rw [coimage_π_comp_degreeThreeCocycleDesc, Preadditive.comp_add,
    coimage_π_comp_degreeThreeCocycleDesc,
    coimage_π_comp_degreeThreeCocycleDesc]
  rfl

/-- The canonical map from degree-three Hom cocycles to `Ext³` supplied by
the first four exact spots of an augmented resolution. -/
def augmentedChainDegreeThreeToExt
    (P C₀ C₁ C₂ C₃ C₄ Y : A)
    (ε : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₁₀ : d₁ ≫ ε = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0) (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₀ : (ShortComplex.mk d₁ ε h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    [Epi ε] (f : DegreeThreeCocycle d₄ (Y := Y)) :
    Ext P Y 3 :=
  let R := threeStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ C₃ ε d₁ d₂ d₃ h₁₀ h₂₁ h₃₂
      hexact₀ hexact₁ hexact₂
  R.connecting Y (degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f)

@[simp]
theorem augmentedChainDegreeThreeToExt_zero
    (P C₀ C₁ C₂ C₃ C₄ Y : A)
    (ε : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₁₀ : d₁ ≫ ε = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0) (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₀ : (ShortComplex.mk d₁ ε h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    [Epi ε] :
    augmentedChainDegreeThreeToExt P C₀ C₁ C₂ C₃ C₄ Y
      ε d₁ d₂ d₃ d₄ h₁₀ h₂₁ h₃₂ h₄₃
      hexact₀ hexact₁ hexact₂ hexact₃ 0 = 0 := by
  let R := threeStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ C₃ ε d₁ d₂ d₃ h₁₀ h₂₁ h₃₂
      hexact₀ hexact₁ hexact₂
  change R.connecting Y
    (degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ 0) = 0
  rw [degreeThreeCocycleDesc_zero]
  exact R.connecting_zero Y

theorem augmentedChainDegreeThreeToExt_add
    (P C₀ C₁ C₂ C₃ C₄ Y : A)
    (ε : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₁₀ : d₁ ≫ ε = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0) (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₀ : (ShortComplex.mk d₁ ε h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    [Epi ε] (f g : DegreeThreeCocycle d₄ (Y := Y)) :
    augmentedChainDegreeThreeToExt P C₀ C₁ C₂ C₃ C₄ Y
      ε d₁ d₂ d₃ d₄ h₁₀ h₂₁ h₃₂ h₄₃
      hexact₀ hexact₁ hexact₂ hexact₃ (f + g) =
    augmentedChainDegreeThreeToExt P C₀ C₁ C₂ C₃ C₄ Y
      ε d₁ d₂ d₃ d₄ h₁₀ h₂₁ h₃₂ h₄₃
      hexact₀ hexact₁ hexact₂ hexact₃ f +
    augmentedChainDegreeThreeToExt P C₀ C₁ C₂ C₃ C₄ Y
      ε d₁ d₂ d₃ d₄ h₁₀ h₂₁ h₃₂ h₄₃
      hexact₀ hexact₁ hexact₂ hexact₃ g := by
  let R := threeStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ C₃ ε d₁ d₂ d₃ h₁₀ h₂₁ h₃₂
      hexact₀ hexact₁ hexact₂
  change R.connecting Y
      (degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ (f + g)) =
    R.connecting Y (degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f) +
      R.connecting Y (degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ g)
  rw [degreeThreeCocycleDesc_add]
  exact R.connecting_add Y
    (show R.K₂ ⟶ Y from
      degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f)
    (show R.K₂ ⟶ Y from
      degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ g)

/-- Under local acyclicity, every `Ext³` class is represented by a
degree-three Hom cocycle. -/
theorem augmentedChainDegreeThreeToExt_surjective
    (P C₀ C₁ C₂ C₃ C₄ Y : A)
    (ε : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₁₀ : d₁ ≫ ε = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0) (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₀ : (ShortComplex.mk d₁ ε h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    [Epi ε]
    [Subsingleton (Ext C₀ Y 3)]
    [Subsingleton (Ext C₁ Y 2)]
    [Subsingleton (Ext C₂ Y 1)] :
    Function.Surjective
      (augmentedChainDegreeThreeToExt P C₀ C₁ C₂ C₃ C₄ Y
        ε d₁ d₂ d₃ d₄ h₁₀ h₂₁ h₃₂ h₄₃
        hexact₀ hexact₁ hexact₂ hexact₃) := by
  let R := threeStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ C₃ ε d₁ d₂ d₃ h₁₀ h₂₁ h₃₂
      hexact₀ hexact₁ hexact₂
  letI : Subsingleton (Ext R.C₀ Y 3) := by
    change Subsingleton (Ext C₀ Y 3)
    infer_instance
  letI : Subsingleton (Ext R.C₁ Y 2) := by
    change Subsingleton (Ext C₁ Y 2)
    infer_instance
  letI : Subsingleton (Ext R.C₂ Y 1) := by
    change Subsingleton (Ext C₂ Y 1)
    infer_instance
  intro z
  obtain ⟨q, hq⟩ := R.connecting_surjective Y z
  change Abelian.coimage d₃ ⟶ Y at q
  let f : DegreeThreeCocycle d₄ (Y := Y) :=
    ⟨Abelian.coimage.π d₃ ≫ q, by
      change d₄ ≫ (Abelian.coimage.π d₃ ≫ q) = 0
      rw [← Category.assoc, Abelian.comp_coimage_π_eq_zero h₄₃, zero_comp]⟩
  refine ⟨f, ?_⟩
  change R.connecting Y (degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f) = z
  rw [show degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f = q by
    apply (cancel_epi (Abelian.coimage.π d₃)).1
    rw [coimage_π_comp_degreeThreeCocycleDesc]]
  exact hq

/-- A degree-three cocycle maps to zero in `Ext³` exactly when it is a
degree-two boundary. -/
theorem augmentedChainDegreeThreeToExt_eq_zero_iff
    (P C₀ C₁ C₂ C₃ C₄ Y : A)
    (ε : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₁₀ : d₁ ≫ ε = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0) (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₀ : (ShortComplex.mk d₁ ε h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    [Epi ε]
    [Subsingleton (Ext C₀ Y 2)]
    [Subsingleton (Ext C₁ Y 1)]
    (f : DegreeThreeCocycle d₄ (Y := Y)) :
    augmentedChainDegreeThreeToExt P C₀ C₁ C₂ C₃ C₄ Y
      ε d₁ d₂ d₃ d₄ h₁₀ h₂₁ h₃₂ h₄₃
      hexact₀ hexact₁ hexact₂ hexact₃ f = 0 ↔
      ∃ q : C₂ ⟶ Y, d₃ ≫ q = f.1 := by
  let R := threeStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ C₃ ε d₁ d₂ d₃ h₁₀ h₂₁ h₃₂
      hexact₀ hexact₁ hexact₂
  letI : Subsingleton (Ext R.C₀ Y 2) := by
    change Subsingleton (Ext C₀ Y 2)
    infer_instance
  letI : Subsingleton (Ext R.C₁ Y 1) := by
    change Subsingleton (Ext C₁ Y 1)
    infer_instance
  have hc := R.connecting_eq_zero_iff Y
    (show R.K₂ ⟶ Y from
      degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f)
  constructor
  · intro h
    have hR : R.connecting Y
        (show R.K₂ ⟶ Y from
          degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f) = 0 := by
      exact h
    obtain ⟨q, hq⟩ := hc.mp hR
    change C₂ ⟶ Y at q
    change Abelian.factorThruCoimage d₃ ≫ q =
      degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f at hq
    refine ⟨q, ?_⟩
    rw [← Abelian.coimage.fac d₃, Category.assoc, hq,
      coimage_π_comp_degreeThreeCocycleDesc]
  · rintro ⟨q, hq⟩
    apply hc.mpr
    refine ⟨q, ?_⟩
    change Abelian.factorThruCoimage d₃ ≫ q =
      degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f
    apply (cancel_epi (Abelian.coimage.π d₃)).1
    rw [← Category.assoc, Abelian.coimage.fac, hq,
      coimage_π_comp_degreeThreeCocycleDesc]

end PfaffianDescent

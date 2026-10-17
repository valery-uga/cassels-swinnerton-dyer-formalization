import PfaffianDescent.CechExtDegreeTwo
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Exact-functor compatibility of the degree-two resolution class

The class produced by a two-step resolution is carried to the class of the
mapped resolution. This also detects the kernel of localization directly
on coefficient cocycles, before choosing a residue coordinate.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PfaffianDescent

universe u v w u' v' w'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

namespace TwoStepResolution

/-- An exact additive functor carries a two-step resolution to a two-step
resolution, keeping its two kernel objects explicit. -/
def map (R : TwoStepResolution C) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    TwoStepResolution D where
  P := F.obj R.P
  C₀ := F.obj R.C₀
  C₁ := F.obj R.C₁
  K₀ := F.obj R.K₀
  K₁ := F.obj R.K₁
  i₀ := F.map R.i₀
  p₀ := F.map R.p₀
  zero₀ := by rw [← F.map_comp, R.zero₀, F.map_zero]
  i₁ := F.map R.i₁
  p₁ := F.map R.p₁
  zero₁ := by rw [← F.map_comp, R.zero₁, F.map_zero]
  exact₀ := R.exact₀.map_of_exact F
  exact₁ := R.exact₁.map_of_exact F

/-- Mapping the global Yoneda class gives the Yoneda class of the mapped
resolution and mapped coefficient homomorphism. -/
theorem connecting_map
    [HasExt.{w} C] [HasExt.{w'} D]
    (R : TwoStepResolution C) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (Y : C) (x : R.K₁ ⟶ Y) :
    (R.connecting Y x).mapExactFunctor F =
      (R.map F).connecting (F.obj Y) (F.map x) := by
  simp only [connecting, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_mk₀]
  rfl

end TwoStepResolution

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- After an exact functor, a resolution coefficient represents zero
precisely when its mapped cocycle extends across the preceding differential.
Only Ext¹-vanishing of the first mapped resolution term is needed. -/
theorem augmentedChainDegreeTwoToExt_map_eq_zero_iff
    [HasExt.{w} C] [HasExt.{w'} D]
    (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P C₀ C₁ C₂ C₃ Y : C)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    [Epi epsilon]
    [Subsingleton (Ext (F.obj C₀) (F.obj Y) 1)]
    (f : DegreeTwoCocycle d₃ (Y := Y)) :
    (augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y
        epsilon d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ f).mapExactFunctor F = 0 ↔
      ∃ q : F.obj C₁ ⟶ F.obj Y, F.map d₂ ≫ q = F.map f.1 := by
  let R := twoStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁
  let x : R.K₁ ⟶ Y := degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f
  change (R.connecting Y x).mapExactFunctor F = 0 ↔ _
  letI : Subsingleton (Ext (R.map F).C₀ (F.obj Y) 1) :=
    ‹Subsingleton (Ext (F.obj C₀) (F.obj Y) 1)›
  erw [TwoStepResolution.connecting_map,
    TwoStepResolution.connecting_eq_zero_iff]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have hπ := coimage_π_comp_degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f
    change F.map (Abelian.factorThruCoimage d₂) ≫ q = F.map x at hq
    rw [← Abelian.coimage.fac d₂, F.map_comp, Category.assoc, hq,
      ← F.map_comp]
    exact congrArg F.map hπ
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    change F.map (Abelian.factorThruCoimage d₂) ≫ q = F.map x
    apply (cancel_epi (F.map (Abelian.coimage.π d₂))).1
    rw [← Category.assoc, ← F.map_comp, Abelian.coimage.fac,
      ← F.map_comp]
    exact hq.trans (congrArg F.map
      (coimage_π_comp_degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f)).symm

end PfaffianDescent

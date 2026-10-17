import PfaffianDescent.CechExtDegreeTwo

/-!
# Unconditional invariance of Cech Ext classes under boundaries

Boundaries map to zero without a local-acyclicity hypothesis. This is the
direction needed to replace arbitrary comparison lifts by explicit ones
when calculating point residues.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PfaffianDescent

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

namespace TwoStepResolution

/-- A coefficient morphism extending across the first resolution term
has zero degree-two connecting class, without acyclicity assumptions. -/
theorem connecting_i₁_comp (R : TwoStepResolution A) (Y : A) (q : R.C₁ ⟶ Y) :
    R.connecting Y (R.i₁ ≫ q) = 0 := by
  simp only [connecting, ← Ext.mk₀_comp_mk₀, R.exact₁.extClass_comp_assoc, Ext.comp_zero]

end TwoStepResolution

section

variable (P C₀ C₁ C₂ C₃ Y : A)
  (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂)
  (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0) (h₃₂ : d₃ ≫ d₂ = 0)
  (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
  (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
  (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact) [Epi epsilon]

set_option backward.isDefEq.respectTransparency false in
/-- A degree-one boundary has zero augmented Ext class, regardless of
whether the cover is acyclic for the coefficient sheaf. -/
theorem augmentedChainDegreeTwoToExt_eq_zero_of_boundary
    (z : DegreeTwoCocycle d₃ (Y := Y)) (q : C₁ ⟶ Y) (hq : d₂ ≫ q = z.1) :
    augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y epsilon d₁ d₂ d₃
      h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ z = 0 := by
  let R := twoStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁
  have hdesc : degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ z =
      Abelian.factorThruCoimage d₂ ≫ q := by
    apply (cancel_epi (Abelian.coimage.π d₂)).1
    rw [coimage_π_comp_degreeTwoCocycleDesc, ← Category.assoc, Abelian.coimage.fac]
    exact hq.symm
  change R.connecting Y (degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ z) = 0
  rw [hdesc]
  exact R.connecting_i₁_comp Y q

set_option backward.isDefEq.respectTransparency false in
/-- Two cocycles differing by a degree-one boundary have the same actual
Ext class. No Ext vanishing is an input to this comparison. -/
theorem augmentedChainDegreeTwoToExt_eq_of_boundary_difference
    (z z' : DegreeTwoCocycle d₃ (Y := Y)) (q : C₁ ⟶ Y)
    (hq : d₂ ≫ q = z.1 - z'.1) :
    augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y epsilon d₁ d₂ d₃
      h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ z =
    augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y epsilon d₁ d₂ d₃
      h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ z' := by
  let F : DegreeTwoCocycle d₃ (Y := Y) →+ Ext P Y 2 :=
    { toFun := augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y epsilon d₁ d₂ d₃
        h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂
      map_zero' := augmentedChainDegreeTwoToExt_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      map_add' := augmentedChainDegreeTwoToExt_add _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ }
  have hz : F (z - z') = 0 :=
    augmentedChainDegreeTwoToExt_eq_zero_of_boundary P C₀ C₁ C₂ C₃ Y
      epsilon d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ (z - z') q hq
  have heq : F z - F z' = 0 := by rw [← map_sub]; exact hz
  exact sub_eq_zero.mp heq

end

end PfaffianDescent

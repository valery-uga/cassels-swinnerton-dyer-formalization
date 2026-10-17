import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Ring.Action.Basic

/-!
# Ring actions induced by actual scheme morphisms

A right action on a scheme induces a left action on its global functions.
If the scheme action preserves a base morphism, the ring action commutes
with the coefficient action induced by that same morphism.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X S : Scheme.{u}} (G : Type v) [Group G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)

/-- Pullback of functions gives the actual ring action induced by a right scheme action. -/
@[instance_reducible]
noncomputable def schemeGlobalSectionAction : MulSemiringAction G Γ(X, ⊤) where
  smul g a := (ρ g).appTop.hom a
  one_smul a := by
    change (ρ 1).appTop.hom a = a
    rw [h₁, Scheme.Hom.id_appTop]
    rfl
  mul_smul g h a := by
    change (ρ (g * h)).appTop.hom a = (ρ g).appTop.hom ((ρ h).appTop.hom a)
    rw [hcomp, Scheme.Hom.comp_appTop]
    rfl
  smul_zero g := (ρ g).appTop.hom.map_zero
  smul_one g := (ρ g).appTop.hom.map_one
  smul_add g := (ρ g).appTop.hom.map_add
  smul_mul g := (ρ g).appTop.hom.map_mul

/-- The constructed action on functions is exactly pullback along the original morphism. -/
theorem schemeGlobalSectionAction_smul (g : G) (a : Γ(X, ⊤)) :
    letI := schemeGlobalSectionAction G ρ h₁ hcomp
    g • a = (ρ g).appTop.hom a := rfl

/-- Preserving the structure morphism makes the induced action fix coefficient functions. -/
theorem schemeGlobalSectionAction_smulComm (f : X ⟶ S)
    (hf : ∀ g : G, ρ g ≫ f = f) :
    letI := schemeGlobalSectionAction G ρ h₁ hcomp
    letI := f.appTop.hom.toAlgebra
    SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  constructor
  intro g r a
  change (ρ g).appTop.hom (f.appTop.hom r * a) =
    f.appTop.hom r * (ρ g).appTop.hom a
  rw [map_mul]
  have he := congrArg (fun z : X ⟶ S ↦ z.appTop) (hf g)
  rw [Scheme.Hom.comp_appTop] at he
  have hr := congrArg (fun z : Γ(S, ⊤) ⟶ Γ(X, ⊤) ↦ z.hom r) he
  exact congrArg (fun b ↦ b * (ρ g).appTop.hom a) hr

end AllCharacteristics

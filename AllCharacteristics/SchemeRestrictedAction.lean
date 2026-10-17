import AllCharacteristics.SchemeGlobalSectionAction
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Restriction of actual scheme actions to stable opens

Right actions restrict to stable open subschemes. Their identity, composition,
and compatibility with the original structure map hold as scheme morphisms.
The induced ring action on functions therefore retains the coefficient map.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X S : Scheme.{u}} (G : Type v) [Group G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (U : X.Opens) (hU : ∀ g : G, (ρ g) ⁻¹ᵁ U = U)

/-- Each original action morphism restricts to the actual stable open subscheme. -/
noncomputable def schemeRestrictedRightAction (g : G) : U.toScheme ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (U.ι ≫ ρ g) (by
    rintro y ⟨x, rfl⟩
    have hx : (U.ι ≫ ρ g) x ∈ U := by
      change x.val ∈ (ρ g) ⁻¹ᵁ U
      rw [hU g]
      exact x.property
    exact ⟨⟨(U.ι ≫ ρ g) x, hx⟩, rfl⟩)

omit [Group G] in
/-- Restriction commutes with the actual open immersion. -/
theorem schemeRestrictedRightAction_ι (g : G) :
    schemeRestrictedRightAction G ρ U hU g ≫ U.ι = U.ι ≫ ρ g := by
  exact IsOpenImmersion.lift_fac _ _ _

include h₁ in
/-- The identity acts as the identity on the actual stable open subscheme. -/
theorem schemeRestrictedRightAction_one :
    schemeRestrictedRightAction G ρ U hU 1 = 𝟙 U.toScheme := by
  apply (cancel_mono U.ι).mp
  rw [schemeRestrictedRightAction_ι, h₁, Category.comp_id, Category.id_comp]

include hcomp in
/-- The restricted morphisms satisfy the right action composition law. -/
theorem schemeRestrictedRightAction_mul (g h : G) :
    schemeRestrictedRightAction G ρ U hU (g * h) =
      schemeRestrictedRightAction G ρ U hU g ≫ schemeRestrictedRightAction G ρ U hU h := by
  apply (cancel_mono U.ι).mp
  rw [schemeRestrictedRightAction_ι, Category.assoc, schemeRestrictedRightAction_ι,
    ← Category.assoc, schemeRestrictedRightAction_ι, Category.assoc, hcomp]

omit [Group G] in
/-- A base morphism preserved by the original action is preserved after restriction. -/
theorem schemeRestrictedRightAction_toBase (f : X ⟶ S)
    (hf : ∀ g : G, ρ g ≫ f = f) (g : G) :
    schemeRestrictedRightAction G ρ U hU g ≫ (U.ι ≫ f) = U.ι ≫ f := by
  rw [← Category.assoc, schemeRestrictedRightAction_ι, Category.assoc, hf g]

/-- Actual pullback of functions supplies the ring action on every stable open. -/
@[instance_reducible]
noncomputable def schemeRestrictedGlobalSectionAction : MulSemiringAction G Γ(U.toScheme, ⊤) :=
  schemeGlobalSectionAction G (schemeRestrictedRightAction G ρ U hU)
    (schemeRestrictedRightAction_one G ρ h₁ U hU)
    (schemeRestrictedRightAction_mul G ρ hcomp U hU)

/-- The restricted function action fixes the coefficients from the original base. -/
theorem schemeRestrictedGlobalSectionAction_smulComm (f : X ⟶ S)
    (hf : ∀ g : G, ρ g ≫ f = f) :
    letI := schemeRestrictedGlobalSectionAction G ρ h₁ hcomp U hU
    letI := (U.ι ≫ f).appTop.hom.toAlgebra
    SMulCommClass G Γ(S, ⊤) Γ(U.toScheme, ⊤) :=
  schemeGlobalSectionAction_smulComm G (schemeRestrictedRightAction G ρ U hU)
    (schemeRestrictedRightAction_one G ρ h₁ U hU)
    (schemeRestrictedRightAction_mul G ρ hcomp U hU) (U.ι ≫ f)
    (schemeRestrictedRightAction_toBase G ρ U hU f hf)

end AllCharacteristics

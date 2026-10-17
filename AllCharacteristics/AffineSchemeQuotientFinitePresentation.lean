import AllCharacteristics.AffineSchemeActionQuotientProperties
import AllCharacteristics.AffineInvariantFiniteType

/-! # Finite presentation of actual affine quotients over the original noetherian base -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X S : Scheme.{u}} [IsAffine X] [IsAffine S] [IsLocallyNoetherian S]
variable (G : Type v) [Group G] [Finite G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (f : X ⟶ S) [LocallyOfFiniteType f] (hf : ∀ g : G, ρ g ≫ f = f)

/-- The actual quotient of an affine finite-type family is locally of finite
presentation over its original affine noetherian base. -/
instance locallyOfFinitePresentation_affineSchemeActionQuotientToBase :
    LocallyOfFinitePresentation (affineSchemeActionQuotientToBase G ρ h₁ hcomp f hf) := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  have : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) := finiteType_globalSectionsOfAffineMap f
  have : LocallyOfFinitePresentation (affineInvariantQuotientToBase Γ(S, ⊤) Γ(X, ⊤) G) := inferInstance
  change LocallyOfFinitePresentation
    (affineInvariantQuotientToBase Γ(S, ⊤) Γ(X, ⊤) G ≫ S.isoSpec.inv)
  infer_instance

end AllCharacteristics

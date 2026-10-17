import AllCharacteristics.SchemeGlobalSectionAction
import Mathlib.Algebra.Algebra.Tower

/-!
# Equivariance and coefficient towers on actual global functions

Equivariant scheme morphisms induce equivariant ring maps on global
functions. The compatible scalar action and the coefficient tower of
composable scheme maps are proved for the actual appTop ring maps.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X Y S : Scheme.{u}} {G : Type v}

/-- An equivariant scheme morphism has an equivariant pullback map on global functions. -/
theorem appTop_equivariant_of_scheme_equivariant
    (ρX : G → (X ⟶ X)) (ρY : G → (Y ⟶ Y)) (a : X ⟶ Y)
    (ha : ∀ g : G, ρX g ≫ a = a ≫ ρY g) (g : G) (s : Γ(Y, ⊤)) :
    (ρX g).appTop.hom (a.appTop.hom s) = a.appTop.hom ((ρY g).appTop.hom s) := by
  have he := congrArg (fun b : X ⟶ Y ↦ b.appTop) (ha g)
  exact congrArg (fun b : Γ(Y, ⊤) ⟶ Γ(X, ⊤) ↦ b.hom s) he

/-- Composition of actual scheme maps induces the corresponding scalar tower on global functions. -/
theorem isScalarTower_globalSectionsOfComposition (a : X ⟶ Y) (b : Y ⟶ S)
    (f : X ⟶ S) (hf : a ≫ b = f) :
    letI := a.appTop.hom.toAlgebra
    letI := b.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) := by
  let := a.appTop.hom.toAlgebra
  let := b.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  change f.appTop.hom = a.appTop.hom.comp b.appTop.hom
  exact congrArg (fun z : X ⟶ S ↦ z.appTop.hom) hf.symm

variable (G) [Group G]
variable (ρX : G → (X ⟶ X)) (hX₁ : ρX 1 = 𝟙 X)
variable (hXcomp : ∀ g h : G, ρX (g * h) = ρX g ≫ ρX h)
variable (ρY : G → (Y ⟶ Y)) (hY₁ : ρY 1 = 𝟙 Y)
variable (hYcomp : ∀ g h : G, ρY (g * h) = ρY g ≫ ρY h)

/-- The constructed actions on global functions are compatible with every equivariant scheme map. -/
theorem smulDistribClass_globalSectionsOfEquivariantMap (a : X ⟶ Y)
    (ha : ∀ g : G, ρX g ≫ a = a ≫ ρY g) :
    letI := schemeGlobalSectionAction G ρX hX₁ hXcomp
    letI := schemeGlobalSectionAction G ρY hY₁ hYcomp
    letI := a.appTop.hom.toAlgebra
    SMulDistribClass G Γ(Y, ⊤) Γ(X, ⊤) := by
  let := schemeGlobalSectionAction G ρX hX₁ hXcomp
  let := schemeGlobalSectionAction G ρY hY₁ hYcomp
  let := a.appTop.hom.toAlgebra
  constructor
  intro g s t
  change (ρX g).appTop.hom (a.appTop.hom s * t) =
    a.appTop.hom ((ρY g).appTop.hom s) * (ρX g).appTop.hom t
  rw [map_mul, appTop_equivariant_of_scheme_equivariant ρX ρY a ha]

end AllCharacteristics

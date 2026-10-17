import AllCharacteristics.AffineQuotientCancellation
import AllCharacteristics.InvariantMapFunctoriality
import AllCharacteristics.SchemeGlobalSectionEquivariance
import AllCharacteristics.AffineSchemeActionQuotientProperties

/-!
# Quotient morphisms induced by equivariant affine scheme maps

Equivariant maps of actual affine schemes induce morphisms between their
constructed invariant quotients. The resulting square with the original
scheme maps commutes. When the original map preserves the common base,
the quotient map preserves it as well.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X Y S : Scheme.{u}} (G : Type v) [Group G]
variable (ρX : G → (X ⟶ X)) (hX₁ : ρX 1 = 𝟙 X)
variable (hXcomp : ∀ g h : G, ρX (g * h) = ρX g ≫ ρX h)
variable (ρY : G → (Y ⟶ Y)) (hY₁ : ρY 1 = 𝟙 Y)
variable (hYcomp : ∀ g h : G, ρY (g * h) = ρY g ≫ ρY h)
variable (p : X ⟶ S) (hp : ∀ g : G, ρX g ≫ p = p)
variable (q : Y ⟶ S) (hq : ∀ g : G, ρY g ≫ q = q)
variable (a : X ⟶ Y) (ha : ∀ g : G, ρX g ≫ a = a ≫ ρY g)

/-- The actual quotient morphism induced by an equivariant map of scheme actions. -/
noncomputable def affineSchemeActionQuotientMorphism :
    affineSchemeActionQuotient G ρX hX₁ hXcomp p hp ⟶
      affineSchemeActionQuotient G ρY hY₁ hYcomp q hq := by
  let := schemeGlobalSectionAction G ρX hX₁ hXcomp
  let := schemeGlobalSectionAction G ρY hY₁ hYcomp
  let := p.appTop.hom.toAlgebra
  let := q.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρX hX₁ hXcomp p hp
  let : SMulCommClass G Γ(S, ⊤) Γ(Y, ⊤) := schemeGlobalSectionAction_smulComm G ρY hY₁ hYcomp q hq
  exact affineInvariantQuotientMorphism Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) G a.appTop.hom
    (fun g s ↦ (appTop_equivariant_of_scheme_equivariant ρX ρY a ha g s).symm)

/-- The constructed quotient maps commute with the original equivariant scheme map. -/
theorem affineSchemeActionQuotientMorphism_square [IsAffine X] [IsAffine Y] :
    affineSchemeActionQuotientMap G ρX hX₁ hXcomp p hp ≫
      affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha =
        a ≫ affineSchemeActionQuotientMap G ρY hY₁ hYcomp q hq := by
  let := schemeGlobalSectionAction G ρX hX₁ hXcomp
  let := schemeGlobalSectionAction G ρY hY₁ hYcomp
  let := p.appTop.hom.toAlgebra
  let := q.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρX hX₁ hXcomp p hp
  let : SMulCommClass G Γ(S, ⊤) Γ(Y, ⊤) := schemeGlobalSectionAction_smulComm G ρY hY₁ hYcomp q hq
  change (X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G) ≫
    affineInvariantQuotientMorphism Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) G a.appTop.hom
      (fun g s ↦ (appTop_equivariant_of_scheme_equivariant ρX ρY a ha g s).symm) =
        a ≫ (Y.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(Y, ⊤) G)
  rw [Category.assoc, affineInvariantQuotientMorphism_square, ← Category.assoc]
  have hn : X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom a.appTop.hom) =
      a ≫ Y.isoSpec.hom := Scheme.isoSpec_hom_naturality a
  rw [hn, Category.assoc]

/-- Equivariant affine maps over the original base induce quotient maps over that same base. -/
theorem affineSchemeActionQuotientMorphism_toBase [IsAffine X] [IsAffine Y] [IsAffine S]
    (haBase : a ≫ q = p) :
    affineSchemeActionQuotientMorphism G ρX hX₁ hXcomp ρY hY₁ hYcomp p hp q hq a ha ≫
      affineSchemeActionQuotientToBase G ρY hY₁ hYcomp q hq =
        affineSchemeActionQuotientToBase G ρX hX₁ hXcomp p hp := by
  apply affineSchemeActionQuotientMap_cancel G ρX hX₁ hXcomp p hp
  rw [← Category.assoc, affineSchemeActionQuotientMorphism_square, Category.assoc,
    affineSchemeActionQuotientMap_toBase, affineSchemeActionQuotientMap_toBase]
  exact haBase

end AllCharacteristics

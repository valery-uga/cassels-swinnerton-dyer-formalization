import AllCharacteristics.SchemeGlobalSectionAction
import AllCharacteristics.AffineInvariantFactorization
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Actual affine-scheme quotients from scheme actions

An actual right action on an affine scheme, preserving a base morphism,
constructs its invariant spectrum and the quotient map from the original
scheme. Its structure map to an affine base and its invariance are proved
using the canonical affine-scheme/global-functions comparison.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X S : Scheme.{u}} (G : Type v) [Group G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (f : X ⟶ S) (hf : ∀ g : G, ρ g ≫ f = f)

/-- The actual invariant spectrum constructed from pullback of functions under the scheme action. -/
noncomputable def affineSchemeActionQuotient : Scheme.{u} := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  exact affineInvariantQuotient Γ(S, ⊤) Γ(X, ⊤) G

/-- The quotient morphism starts from the original affine scheme. -/
noncomputable def affineSchemeActionQuotientMap [IsAffine X] :
    X ⟶ affineSchemeActionQuotient G ρ h₁ hcomp f hf := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  exact X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G

/-- The invariant quotient retains its structure morphism to the original affine base scheme. -/
noncomputable def affineSchemeActionQuotientToBase [IsAffine S] :
    affineSchemeActionQuotient G ρ h₁ hcomp f hf ⟶ S := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  exact affineInvariantQuotientToBase Γ(S, ⊤) Γ(X, ⊤) G ≫ S.isoSpec.inv

/-- The actual quotient factorization preserves the original family morphism. -/
theorem affineSchemeActionQuotientMap_toBase [IsAffine X] [IsAffine S] :
    affineSchemeActionQuotientMap G ρ h₁ hcomp f hf ≫
      affineSchemeActionQuotientToBase G ρ h₁ hcomp f hf = f := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  change (X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G) ≫
    (affineInvariantQuotientToBase Γ(S, ⊤) Γ(X, ⊤) G ≫ S.isoSpec.inv) = f
  rw [Category.assoc, ← Category.assoc (affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G),
    affineInvariantQuotientMap_toBase]
  change X.isoSpec.hom ≫ Spec.map f.appTop ≫ S.isoSpec.inv = f
  rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The quotient morphism is invariant under every original scheme action morphism. -/
theorem affineSchemeActionQuotientMap_invariant [IsAffine X] (g : G) :
    ρ g ≫ affineSchemeActionQuotientMap G ρ h₁ hcomp f hf =
      affineSchemeActionQuotientMap G ρ h₁ hcomp f hf := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  change ρ g ≫ (X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G) =
    X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G
  rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc]
  exact congrArg (fun z ↦ X.isoSpec.hom ≫ z)
    (affineInvariantQuotientMap_invariant Γ(S, ⊤) Γ(X, ⊤) G g)

end AllCharacteristics

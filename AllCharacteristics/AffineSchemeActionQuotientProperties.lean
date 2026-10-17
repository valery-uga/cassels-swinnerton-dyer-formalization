import AllCharacteristics.AffineSchemeActionQuotient
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Geometric properties of quotients constructed from affine scheme actions

The quotient map from the original affine scheme is integral and surjective.
For a family of finite type over an affine base it is finite and proper.
The required finite-type assertion for the actual global-function algebra is
proved from the given morphism of affine schemes.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X S : Scheme.{u}}

/-- A finite-type map between actual affine schemes gives a finite-type global-function algebra. -/
theorem finiteType_globalSectionsOfAffineMap (f : X ⟶ S)
    [IsAffine X] [IsAffine S] [LocallyOfFiniteType f] :
    letI := f.appTop.hom.toAlgebra
    Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) := by
  let := f.appTop.hom.toAlgebra
  apply RingHom.finiteType_algebraMap.mp
  change RingHom.FiniteType f.appTop.hom
  have he : f.appLE ⊤ ⊤ le_rfl = f.appTop := f.appLE_eq_app
  rw [← he]
  exact f.finiteType_appLE (isAffineOpen_top S) (isAffineOpen_top X) le_rfl

variable (G : Type v) [Group G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (f : X ⟶ S) (hf : ∀ g : G, ρ g ≫ f = f)

/-- The constructed quotient is an actual affine scheme. -/
instance isAffine_affineSchemeActionQuotient :
    IsAffine (affineSchemeActionQuotient G ρ h₁ hcomp f hf) := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  change IsAffine (Spec (.of (FixedPoints.subalgebra Γ(S, ⊤) Γ(X, ⊤) G)))
  infer_instance

/-- An affine action quotient is integral as soon as the original affine
scheme has a domain of global functions.  This is the local chart input for
integrality of the configuration quotients used in generic specialization. -/
theorem isIntegral_affineSchemeActionQuotient_of_globalSections_domain
    [IsDomain Γ(X, ⊤)] :
    IsIntegral (affineSchemeActionQuotient G ρ h₁ hcomp f hf) := by
  letI := schemeGlobalSectionAction G ρ h₁ hcomp
  letI := f.appTop.hom.toAlgebra
  letI : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  change IsIntegral (Spec (.of (FixedPoints.subalgebra Γ(S, ⊤) Γ(X, ⊤) G)))
  infer_instance

variable [Finite G] [IsAffine X]

/-- The quotient morphism from the original affine scheme is integral. -/
instance isIntegralHom_affineSchemeActionQuotientMap :
    IsIntegralHom (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  change IsIntegralHom (X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G)
  infer_instance

/-- The quotient morphism from the original affine scheme is surjective. -/
instance surjective_affineSchemeActionQuotientMap :
    Surjective (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  change Surjective (X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G)
  infer_instance

/-- A finite-type affine family has a finite quotient morphism for the actual scheme action. -/
instance isFinite_affineSchemeActionQuotientMap [IsAffine S] [LocallyOfFiniteType f] :
    IsFinite (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  have : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) := finiteType_globalSectionsOfAffineMap f
  change IsFinite (X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G)
  infer_instance

/-- The quotient morphism of a finite-type affine family is proper. -/
instance isProper_affineSchemeActionQuotientMap [IsAffine S] [LocallyOfFiniteType f] :
    IsProper (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) := by
  infer_instance

end AllCharacteristics

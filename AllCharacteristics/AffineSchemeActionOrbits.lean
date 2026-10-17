import AllCharacteristics.AffineSchemeActionQuotientProperties
import AllCharacteristics.InvariantPrimeOrbits

/-!
# Fibers of the quotient map from the original affine scheme

The constructed quotient map identifies two original scheme points exactly
when one is carried to the other by an original action morphism. The proof
uses the canonical global-functions comparison and retains the actual
scheme action, rather than assuming an orbit description of the quotient.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X S : Scheme.{u}} [IsAffine X] (G : Type v) [Group G] [Finite G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (f : X ⟶ S) (hf : ∀ g : G, ρ g ≫ f = f)

/-- Actual quotient fibers are exactly the orbits of the original scheme action. -/
theorem affineSchemeActionQuotientMap_eq_iff_orbit (x y : X) :
    affineSchemeActionQuotientMap G ρ h₁ hcomp f hf x =
      affineSchemeActionQuotientMap G ρ h₁ hcomp f hf y ↔ ∃ g : G, ρ g x = y := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) := schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  constructor
  · intro h
    change affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G (X.isoSpec.hom x) =
      affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G (X.isoSpec.hom y) at h
    obtain ⟨g, hg⟩ := (affineInvariantQuotientMap_eq_iff_comap Γ(S, ⊤) Γ(X, ⊤) G
      (X.isoSpec.hom x) (X.isoSpec.hom y)).mp h
    refine ⟨g, X.isoSpec.hom.isOpenEmbedding.injective ?_⟩
    have he : PrimeSpectrum.comap (MulSemiringAction.toRingHom G Γ(X, ⊤) g) (X.isoSpec.hom x) =
        X.isoSpec.hom (ρ g x) :=
      congrArg (fun a : X ⟶ Spec Γ(X, ⊤) ↦ a x) (Scheme.isoSpec_hom_naturality (ρ g))
    exact he.symm.trans hg
  · rintro ⟨g, hg⟩
    have hi := congrArg (fun a : X ⟶ affineSchemeActionQuotient G ρ h₁ hcomp f hf ↦ a x)
      (affineSchemeActionQuotientMap_invariant G ρ h₁ hcomp f hf g)
    change affineSchemeActionQuotientMap G ρ h₁ hcomp f hf (ρ g x) =
      affineSchemeActionQuotientMap G ρ h₁ hcomp f hf x at hi
    rw [hg] at hi
    exact hi.symm

end AllCharacteristics

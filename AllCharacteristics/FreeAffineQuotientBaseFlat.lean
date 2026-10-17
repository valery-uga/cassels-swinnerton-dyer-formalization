import AllCharacteristics.FreeActionInvariantRetraction
import AllCharacteristics.AffineSchemeFreeAction
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Flatness over the original base for actual free affine quotients -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v

/-- The actual free invariant quotient is flat over the original coefficient
ring whenever the original algebra is flat over that ring. -/
theorem flat_affineInvariantQuotientToBase_of_free
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    Flat (affineInvariantQuotientToBase R B G) := by
  let : Fintype G := Fintype.ofFinite G
  have : Module.Flat R (FixedPoints.subalgebra R B G) :=
    flat_fixedSubalgebra_of_free_action R B G hfree
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R B G))))
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- An actual geometrically free affine-scheme quotient preserves flatness
of the original family over its original affine base. -/
theorem flat_affineSchemeActionQuotientToBase_of_free
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (G : Type v) [Group G] [Finite G]
    (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
    (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
    (f : X ⟶ S) [Flat f] (hf : ∀ g : G, ρ g ≫ f = f)
    (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X) (g : G),
      g ≠ 1 → a ≫ ρ g ≠ a) :
    Flat (affineSchemeActionQuotientToBase G ρ h₁ hcomp f hf) := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  have hI : ∀ g : G, g ≠ 1 → actionDifferenceIdeal Γ(X, ⊤) G g = ⊤ := by
    intro g hg
    exact actionDifferenceIdeal_eq_top_of_scheme_free G ρ h₁ hcomp g
      (fun K _ a ↦ hfree K a g hg)
  have : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
    RingHom.flat_algebraMap_iff.mp (show (algebraMap Γ(S, ⊤) Γ(X, ⊤)).Flat from f.flat_appTop)
  have : Flat (affineInvariantQuotientToBase Γ(S, ⊤) Γ(X, ⊤) G) :=
    flat_affineInvariantQuotientToBase_of_free Γ(S, ⊤) Γ(X, ⊤) G hI
  change Flat (affineInvariantQuotientToBase Γ(S, ⊤) Γ(X, ⊤) G ≫ S.isoSpec.inv)
  infer_instance

end AllCharacteristics

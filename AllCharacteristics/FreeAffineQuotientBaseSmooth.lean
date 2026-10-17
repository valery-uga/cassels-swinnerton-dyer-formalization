import AllCharacteristics.FreeActionInvariantSmooth
import AllCharacteristics.AffineSchemeFreeAction
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness over the original base for actual free affine quotients -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v

/-- The actual free invariant quotient is smooth over the original noetherian coefficient
ring whenever the original algebra is smooth over that ring. -/
theorem smooth_affineInvariantQuotientToBase_of_free
    (R B : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    Smooth (affineInvariantQuotientToBase R B G) := by
  let : Fintype G := Fintype.ofFinite G
  have : Algebra.Smooth R (FixedPoints.subalgebra R B G) :=
    smooth_fixedSubalgebra_of_free_action R B G hfree
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R B G))))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

/-- An actual geometrically free affine-scheme quotient preserves smoothness
of the original family over its original affine noetherian base. -/
theorem smooth_affineSchemeActionQuotientToBase_of_free
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] [IsLocallyNoetherian S]
    (G : Type v) [Group G] [Finite G]
    (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
    (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
    (f : X ⟶ S) [Smooth f] (hf : ∀ g : G, ρ g ≫ f = f)
    (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X) (g : G),
      g ≠ 1 → a ≫ ρ g ≠ a) :
    Smooth (affineSchemeActionQuotientToBase G ρ h₁ hcomp f hf) := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  have hI : ∀ g : G, g ≠ 1 → actionDifferenceIdeal Γ(X, ⊤) G g = ⊤ := by
    intro g hg
    exact actionDifferenceIdeal_eq_top_of_scheme_free G ρ h₁ hcomp g
      (fun K _ a ↦ hfree K a g hg)
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  have : Algebra.Smooth Γ(S, ⊤) Γ(X, ⊤) :=
    RingHom.smooth_algebraMap.mp (show (algebraMap Γ(S, ⊤) Γ(X, ⊤)).Smooth from
      (HasRingHomProperty.iff_of_isAffine (P := @Smooth.{u})).mp inferInstance)
  have : Smooth (affineInvariantQuotientToBase Γ(S, ⊤) Γ(X, ⊤) G) :=
    smooth_affineInvariantQuotientToBase_of_free Γ(S, ⊤) Γ(X, ⊤) G hI
  change Smooth (affineInvariantQuotientToBase Γ(S, ⊤) Γ(X, ⊤) G ≫ S.isoSpec.inv)
  infer_instance

end AllCharacteristics

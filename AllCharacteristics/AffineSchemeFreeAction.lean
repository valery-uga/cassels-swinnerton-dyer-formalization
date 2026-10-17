import AllCharacteristics.ActionFixedIdealFieldCriterion
import AllCharacteristics.FreeActionEtale
import AllCharacteristics.AffineSchemeActionQuotient

/-! # Étaleness of actual affine scheme quotients from geometric freeness -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X S : Scheme.{u}} [IsAffine X] (G : Type v) [Group G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)

/-- An affine scheme action without a fixed field-valued point has the unit
ideal as its actual action-difference ideal of global functions. -/
theorem actionDifferenceIdeal_eq_top_of_scheme_free (g : G)
    (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X), a ≫ ρ g ≠ a) :
    letI := schemeGlobalSectionAction G ρ h₁ hcomp
    actionDifferenceIdeal Γ(X, ⊤) G g = ⊤ := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  apply actionDifferenceIdeal_eq_top_of_no_fixed_field_maps
  intro K _ a ha
  change a.comp (ρ g).appTop.hom = a at ha
  have hs : Spec.map (CommRingCat.ofHom a) ≫ Spec.map (ρ g).appTop =
      Spec.map (CommRingCat.ofHom a) := by
    rw [← Spec.map_comp]
    exact congrArg (fun z : Γ(X, ⊤) →+* K ↦ Spec.map (CommRingCat.ofHom z)) ha
  apply hfree K (Spec.map (CommRingCat.ofHom a) ≫ X.isoSpec.inv)
  apply (cancel_mono X.isoSpec.hom).mp
  rw [Category.assoc, Category.assoc, ← Scheme.isoSpec_hom_naturality,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hs

/-- The actual affine-scheme quotient of a geometrically free finite-group
action is étale, over the original coefficient scheme. -/
theorem etale_affineSchemeActionQuotientMap_of_free [Finite G]
    (f : X ⟶ S) (hf : ∀ g : G, ρ g ≫ f = f)
    (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X) (g : G),
      g ≠ 1 → a ≫ ρ g ≠ a) :
    Etale (affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  have hI : ∀ g : G, g ≠ 1 → actionDifferenceIdeal Γ(X, ⊤) G g = ⊤ := by
    intro g hg
    exact actionDifferenceIdeal_eq_top_of_scheme_free G ρ h₁ hcomp g
      (fun K _ a ↦ hfree K a g hg)
  have : Etale (affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G) :=
    etale_affineInvariantQuotientMap_of_free_action Γ(S, ⊤) Γ(X, ⊤) G hI
  change Etale (X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G)
  infer_instance

end AllCharacteristics

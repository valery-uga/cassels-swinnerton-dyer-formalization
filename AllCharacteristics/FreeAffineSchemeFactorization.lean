import AllCharacteristics.FreeActionAffineFactorization
import AllCharacteristics.AffineSchemeFreeAction

/-! # The categorical property of an actual free affine-scheme quotient -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} [IsAffine X] (G : Type) [Group G] [Finite G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (f : X ⟶ S) (hf : ∀ g : G, ρ g ≫ f = f)

/-- The original affine-scheme quotient has the categorical universal property
for morphisms to arbitrary schemes when the action has no fixed field points. -/
theorem existsUnique_freeAffineSchemeActionFactor
    (hfree : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ X) (g : G),
      g ≠ 1 → x ≫ ρ g ≠ x)
    {T : Scheme.{u}} (a : X ⟶ T) (ha : ∀ g : G, ρ g ≫ a = a) :
    ∃! b : affineSchemeActionQuotient G ρ h₁ hcomp f hf ⟶ T,
      affineSchemeActionQuotientMap G ρ h₁ hcomp f hf ≫ b = a := by
  let := schemeGlobalSectionAction G ρ h₁ hcomp
  let := f.appTop.hom.toAlgebra
  let : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  have hI : ∀ g : G, g ≠ 1 → actionDifferenceIdeal Γ(X, ⊤) G g = ⊤ := by
    intro g hg
    exact actionDifferenceIdeal_eq_top_of_scheme_free G ρ h₁ hcomp g
      (fun K _ x ↦ hfree K x g hg)
  have ha' : ∀ g : G,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, ⊤) g)) ≫
        (X.isoSpec.inv ≫ a) = X.isoSpec.inv ≫ a := by
    intro g
    change Spec.map (ρ g).appTop ≫ (X.isoSpec.inv ≫ a) = X.isoSpec.inv ≫ a
    apply (cancel_epi X.isoSpec.hom).mp
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id_assoc, ha]
  obtain ⟨b, hb, hu⟩ := existsUnique_affineInvariantSchemeFactor_of_free
    Γ(S, ⊤) Γ(X, ⊤) G hI (X.isoSpec.inv ≫ a) ha'
  refine ⟨b, ?_, ?_⟩
  · change (X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G) ≫ b = a
    rw [Category.assoc, hb, Iso.hom_inv_id_assoc]
  · intro c hc
    change affineInvariantQuotient Γ(S, ⊤) Γ(X, ⊤) G ⟶ T at c
    apply hu c
    change (X.isoSpec.hom ≫ affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G) ≫ c = a at hc
    apply (cancel_epi X.isoSpec.hom).mp
    rw [← Category.assoc X.isoSpec.hom (affineInvariantQuotientMap Γ(S, ⊤) Γ(X, ⊤) G) c,
      hc, Iso.hom_inv_id_assoc]

end AllCharacteristics

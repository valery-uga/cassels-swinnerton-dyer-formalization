import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Away.Basic

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}

/-- The ring map on affine coordinate functions of an arbitrary scheme morphism. -/
noncomputable def affineFunctionHom (f : X ⟶ Spec (.of R)) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom

lemma affineFunctionHom_comp (f : X ⟶ Y) (g : Y ⟶ Spec (.of R)) :
    affineFunctionHom (f ≫ g) = f.appTop.hom.comp (affineFunctionHom g) := by
  unfold affineFunctionHom
  rw [Scheme.Hom.comp_appTop, ← Category.assoc]
  rfl

lemma affineFunctionHom_comp_Spec (f : X ⟶ Spec (.of S)) (φ : R →+* S) :
    affineFunctionHom (f ≫ Spec.map (CommRingCat.ofHom φ)) =
      (affineFunctionHom f).comp φ := by
  unfold affineFunctionHom
  rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- Construct a morphism to an affine scheme from its coordinate functions. -/
noncomputable def morphismFromAffineFunctions (X : Scheme.{u}) (φ : R →+* Γ(X, ⊤)) :
    X ⟶ Spec (.of R) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)

lemma affineFunctionHom_from (φ : R →+* Γ(X, ⊤)) :
    affineFunctionHom (morphismFromAffineFunctions X φ) = φ := by
  unfold morphismFromAffineFunctions affineFunctionHom
  rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

lemma from_affineFunctionHom (f : X ⟶ Spec (.of R)) :
    morphismFromAffineFunctions X (affineFunctionHom f) = f := by
  unfold morphismFromAffineFunctions affineFunctionHom
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) = _
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

lemma affineFunctionHom_injective :
    Function.Injective (affineFunctionHom (X := X) (R := R)) := by
  intro f g h
  rw [← from_affineFunctionHom f, ← from_affineFunctionHom g, h]

lemma morphismFromAffineFunctions_comp_Spec (φ : S →+* Γ(X, ⊤)) (ψ : R →+* S) :
    morphismFromAffineFunctions X φ ≫ Spec.map (CommRingCat.ofHom ψ) =
      morphismFromAffineFunctions X (φ.comp ψ) := by
  unfold morphismFromAffineFunctions
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- A morphism factors through a principal localization when its defining function is a unit. -/
noncomputable def affineLocalizationLift (f : X ⟶ Spec (.of R)) (r : R)
    (h : IsUnit (affineFunctionHom f r)) : X ⟶ Spec (.of (Localization.Away r)) :=
  morphismFromAffineFunctions X (IsLocalization.Away.lift r h)

lemma affineLocalizationLift_fac (f : X ⟶ Spec (.of R)) (r : R)
    (h : IsUnit (affineFunctionHom f r)) :
    affineLocalizationLift f r h ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) = f := by
  unfold affineLocalizationLift
  rw [morphismFromAffineFunctions_comp_Spec, IsLocalization.Away.lift_comp,
    from_affineFunctionHom]

/-- This factorization test holds on arbitrary schemes, including nonreduced ones. -/
lemma affineLocalization_factor_iff (f : X ⟶ Spec (.of R)) (r : R) :
    (∃ g : X ⟶ Spec (.of (Localization.Away r)),
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) = f) ↔
      IsUnit (affineFunctionHom f r) := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [affineFunctionHom_comp_Spec]
    exact (IsLocalization.Away.algebraMap_isUnit r).map (affineFunctionHom g)
  · intro h
    exact ⟨affineLocalizationLift f r h, affineLocalizationLift_fac f r h⟩

end
end PfaffianDescent

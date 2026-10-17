import AllCharacteristics.FiniteSubschemeFromImmersion

/-!
# The schemes underlying transported finite subschemes

Changing an ambient presentation by an isomorphism preserves the actual
finite scheme. These identifications retain its points, not only its rank.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AllCharacteristics

universe u

/-- Having exactly one point is preserved by an isomorphism of schemes. -/
theorem nonempty_subsingleton_of_schemeIso {X Y : Scheme.{u}} (e : X ≅ Y)
    (h : Nonempty Y ∧ Subsingleton Y) : Nonempty X ∧ Subsingleton X := by
  obtain ⟨y⟩ := h.1
  exact ⟨⟨e.inv y⟩, ⟨fun a b => e.hom.homeomorph.injective (h.2.elim _ _)⟩⟩

namespace FiniteSubschemeDatum

/-- Pullback by an isomorphism of ambient schemes leaves the finite
subscheme isomorphic to the original one. -/
noncomputable def baseChangeSubschemeIso
    {X Y S T : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ T} {n : ℕ}
    (g : X ⟶ Y) [IsIso g] (b : S ⟶ T) (h : IsPullback g p q b)
    (D : FiniteSubschemeDatum q n) :
    (baseChange g b h D).val.subscheme ≅ D.val.subscheme :=
  D.val.comapIso g ≪≫ asIso (pullback.snd g D.val.subschemeι)

/-- The inverse identification from a finite scheme to its pullback has the
expected map into the new ambient scheme. -/
@[reassoc]
theorem baseChangeSubschemeIso_inv_ι
    {X Y S T : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ T} {n : ℕ}
    (g : X ⟶ Y) [IsIso g] (b : S ⟶ T) (h : IsPullback g p q b)
    (D : FiniteSubschemeDatum q n) :
    (baseChangeSubschemeIso g b h D).inv ≫
        (baseChange g b h D).val.subschemeι =
      D.val.subschemeι ≫ inv g := by
  change (D.val.comapIso g ≪≫ asIso (pullback.snd g D.val.subschemeι)).inv ≫
      (D.val.comap g).subschemeι = D.val.subschemeι ≫ inv g
  apply (cancel_mono g).1
  conv_rhs => rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  simp only [Iso.trans_inv, Category.assoc,
    Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc]
  rw [pullback.condition]
  change (asIso (pullback.snd g D.val.subschemeι)).inv ≫
      (asIso (pullback.snd g D.val.subschemeι)).hom ≫ D.val.subschemeι =
    D.val.subschemeι
  rw [Iso.inv_hom_id_assoc]

/-- The inverse identification from the original finite scheme to its
pullback also preserves the structure morphism to the new base. -/
@[reassoc]
theorem baseChangeSubschemeIso_inv_toBase
    {X Y S T : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ T} {n : ℕ}
    (g : X ⟶ Y) [IsIso g] (b : S ⟶ T) (h : IsPullback g p q b)
    (D : FiniteSubschemeDatum q n) :
    (baseChangeSubschemeIso g b h D).inv ≫
        (baseChange g b h D).val.subschemeι ≫ p ≫ b =
      D.val.subschemeι ≫ q := by
  rw [baseChangeSubschemeIso_inv_ι_assoc]
  rw [← h.w]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

/-- The image construction used for ambient transport does not change
the embedded finite scheme. -/
noncomputable def transportAlongAmbientIsoSubschemeIso
    {T X Y : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T)
    (e : X ≅ Y) (he : e.hom ≫ g = f) {n : ℕ}
    (D : FiniteSubschemeDatum g n) :
    (transportAlongAmbientIso f g e he D).val.subscheme ≅ D.val.subscheme := by
  change (D.val.subschemeι ≫ e.inv).image ≅ D.val.subscheme
  exact (asIso (D.val.subschemeι ≫ e.inv).toImage).symm

/-- The inverse identification from the original finite scheme to its
transport has the expected ambient map: first embed in the old ambient and
then apply the inverse ambient isomorphism. -/
@[reassoc]
theorem transportAlongAmbientIsoSubschemeIso_inv_ι
    {T X Y : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T)
    (e : X ≅ Y) (he : e.hom ≫ g = f) {n : ℕ}
    (D : FiniteSubschemeDatum g n) :
    (transportAlongAmbientIsoSubschemeIso f g e he D).inv ≫
        (transportAlongAmbientIso f g e he D).val.subschemeι =
      D.val.subschemeι ≫ e.inv := by
  change (asIso (D.val.subschemeι ≫ e.inv).toImage).hom ≫
      (D.val.subschemeι ≫ e.inv).ker.subschemeι =
    D.val.subschemeι ≫ e.inv
  exact (D.val.subschemeι ≫ e.inv).toImage_imageι

/-- Ambient transport along an isomorphism preserves the finite scheme's
structure morphism to the common base. -/
@[reassoc]
theorem transportAlongAmbientIsoSubschemeIso_inv_toBase
    {T X Y : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T)
    (e : X ≅ Y) (he : e.hom ≫ g = f) {n : ℕ}
    (D : FiniteSubschemeDatum g n) :
    (transportAlongAmbientIsoSubschemeIso f g e he D).inv ≫
        (transportAlongAmbientIso f g e he D).val.subschemeι ≫ f =
      D.val.subschemeι ≫ g := by
  rw [transportAlongAmbientIsoSubschemeIso_inv_ι_assoc]
  rw [← he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end FiniteSubschemeDatum

end AllCharacteristics

import AllCharacteristics.FiniteSubschemeFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Embedded finite subschemes as ideal-defined data

A finite flat closed immersion of fixed rank determines a point of the
subscheme moduli problem. The kernel ideal's closed subscheme is isomorphic to
the original embedded scheme, with the embedding and base map preserved.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [hi : IsClosedImmersion i] (f : X ⟶ S)
variable [IsFinite (i ≫ f)] [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)]
variable (n : ℕ) (hn : ∀ s : S, (i ≫ f).finrank s = n)

/-- An actual finite flat embedded subscheme defines an ideal-based datum of its rank. -/
noncomputable def finiteSubschemeDatumOfClosedImmersion : FiniteSubschemeDatum f n := by
  have hc : (asIso i.toImage).hom ≫ (i.ker.subschemeι ≫ f) = i ≫ f := by
    rw [← Category.assoc]
    exact congrArg (fun a ↦ a ≫ f) i.toImage_imageι
  have he : (asIso i.toImage).inv ≫ (i ≫ f) = i.ker.subschemeι ≫ f :=
    (asIso i.toImage).inv_comp_eq.mpr hc.symm
  refine ⟨i.ker, ?_, ?_, ?_, ?_⟩
  · rw [← he]
    infer_instance
  · rw [← he]
    infer_instance
  · rw [← he]
    infer_instance
  · intro s
    rw [← he, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hn s

/-- The datum's ideal is exactly the original immersion's kernel ideal. -/
theorem finiteSubschemeDatumOfClosedImmersion_ideal :
    (finiteSubschemeDatumOfClosedImmersion i f n hn).val = i.ker := rfl

include hi

/-- The original embedded scheme identifies with the datum's actual closed subscheme. -/
noncomputable def finiteSubschemeDatumOfClosedImmersionIso :
    Z ≅ (finiteSubschemeDatumOfClosedImmersion i f n hn).val.subscheme :=
  by
    change Z ≅ i.image
    exact asIso i.toImage

/-- The identification preserves the original closed immersion. -/
theorem finiteSubschemeDatumOfClosedImmersionIso_hom_ι :
    (finiteSubschemeDatumOfClosedImmersionIso i f n hn).hom ≫
      (finiteSubschemeDatumOfClosedImmersion i f n hn).val.subschemeι = i :=
  i.toImage_imageι

/-- The identification preserves the original finite flat structure map. -/
theorem finiteSubschemeDatumOfClosedImmersionIso_hom_toBase :
    (finiteSubschemeDatumOfClosedImmersionIso i f n hn).hom ≫
      (finiteSubschemeDatumOfClosedImmersion i f n hn).val.subschemeι ≫ f = i ≫ f := by
  rw [← Category.assoc, finiteSubschemeDatumOfClosedImmersionIso_hom_ι]

/-- If the original finite closed immersion is étale over the base, then the
ideal-defined datum obtained from its kernel is étale over the same base.
The datum's closed subscheme is canonically isomorphic to the original
source, so this transports étaleness across that isomorphism. -/
theorem finiteSubschemeDatumOfClosedImmersion_toBase_etale [Etale (i ≫ f)] :
    Etale ((finiteSubschemeDatumOfClosedImmersion i f n hn).val.subschemeι ≫ f) := by
  let e := finiteSubschemeDatumOfClosedImmersionIso i f n hn
  have he : e.hom ≫ (finiteSubschemeDatumOfClosedImmersion i f n hn).val.subschemeι ≫
      f = i ≫ f :=
    finiteSubschemeDatumOfClosedImmersionIso_hom_toBase i f n hn
  have hrewrite :
      (finiteSubschemeDatumOfClosedImmersion i f n hn).val.subschemeι ≫ f =
        e.inv ≫ (i ≫ f) := by
    calc
      _ = (𝟙 _) ≫ _ := rfl
      _ = (e.inv ≫ e.hom) ≫ _ := by rw [e.inv_hom_id]
      _ = e.inv ≫ (e.hom ≫ _) := Category.assoc _ _ _
      _ = e.inv ≫ (i ≫ f) := congrArg (fun g ↦ e.inv ≫ g) he
  rw [hrewrite]
  letI : IsIso e.inv := by
    dsimp [e]
    infer_instance
  letI : IsOpenImmersion e.inv := by infer_instance
  letI : Etale e.inv := by infer_instance
  exact Etale.etale_comp (f := e.inv) (i ≫ f)

/-- Transport a finite flat subscheme across an isomorphism of ambient schemes
over a field.  This is used when a coefficient-changed cubic is identified
with the corresponding categorical generic fiber. -/
noncomputable def FiniteSubschemeDatum.transportAlongAmbientIso
    {T X Y : Scheme.{u}}
    (f : X ⟶ T) (g : Y ⟶ T)
    (e : X ≅ Y) (he : e.hom ≫ g = f)
    {n : ℕ} (D : FiniteSubschemeDatum g n) :
    FiniteSubschemeDatum f n := by
  let i : D.val.subscheme ⟶ X := D.val.subschemeι ≫ e.inv
  have hi : i ≫ f = D.val.subschemeι ≫ g := by
    change D.val.subschemeι ≫ e.inv ≫ f = D.val.subschemeι ≫ g
    rw [← he]
    simp
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ f) := by
    rw [hi]
    exact D.property.1
  haveI : Flat (i ≫ f) := by
    rw [hi]
    exact D.property.2.1
  haveI : LocallyOfFinitePresentation (i ≫ f) := by
    rw [hi]
    exact D.property.2.2.1
  exact finiteSubschemeDatumOfClosedImmersion i f n (fun s ↦ by
    rw [hi]
    exact D.property.2.2.2 s)

namespace FiniteSubschemeDatum

omit [IsClosedImmersion i] in
/-- Étaleness of an ideal-defined finite subscheme is stable under a
Cartesian change of its ambient family. -/
theorem baseChange_toBase_etale
    {X Y S T : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ T} {n : ℕ}
    (g : X ⟶ Y) (b : S ⟶ T) (h : IsPullback g p q b)
    (D : FiniteSubschemeDatum q n) [Etale (D.val.subschemeι ≫ q)] :
    Etale ((FiniteSubschemeDatum.baseChange g b h D).val.subschemeι ≫ p) := by
  change Etale ((D.val.comap g).subschemeι ≫ p)
  exact MorphismProperty.of_isPullback (P := @Etale.{u})
    (isPullback_idealSubschemeFamily D.val g p q b h) inferInstance

omit [IsClosedImmersion i] in
theorem transportAlongAmbientIso_toBase_etale
    {T X Y : Scheme.{u}}
    (f : X ⟶ T) (g : Y ⟶ T)
    (e : X ≅ Y) (he : e.hom ≫ g = f)
    {n : ℕ} (D : FiniteSubschemeDatum g n)
    [Etale (D.val.subschemeι ≫ g)] :
    Etale ((FiniteSubschemeDatum.transportAlongAmbientIso f g e he D).val.subschemeι ≫ f) := by
  let i : D.val.subscheme ⟶ X := D.val.subschemeι ≫ e.inv
  have hi : i ≫ f = D.val.subschemeι ≫ g := by
    change D.val.subschemeι ≫ e.inv ≫ f = D.val.subschemeι ≫ g
    rw [← he]
    simp
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ f) := by
    rw [hi]
    exact D.property.1
  haveI : Flat (i ≫ f) := by
    rw [hi]
    exact D.property.2.1
  haveI : LocallyOfFinitePresentation (i ≫ f) := by
    rw [hi]
    exact D.property.2.2.1
  haveI : Etale (i ≫ f) := by
    rw [hi]
    infer_instance
  change Etale ((finiteSubschemeDatumOfClosedImmersion i f n (fun s ↦ by
    rw [hi]
    exact D.property.2.2.2 s)).val.subschemeι ≫ f)
  exact finiteSubschemeDatumOfClosedImmersion_toBase_etale i f n _

end FiniteSubschemeDatum

end AllCharacteristics

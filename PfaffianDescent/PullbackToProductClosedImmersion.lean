import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# A relative fibre product as a closed subscheme of an ordinary product

Over a separated base, the canonical map from a fibre product to the
ordinary product is a closed immersion: it is the pullback of the diagonal
of the base. This supplies the categorical embedding used in local
projective incidence arguments.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The comparison from a fibre product to the ordinary product is the
pullback of the diagonal of the common base. -/
theorem isPullback_pullbackToProd_diagonal :
    IsPullback
      (pullback.fst f g ≫ f)
      (prod.lift (pullback.fst f g) (pullback.snd f g))
      (prod.lift (𝟙 S) (𝟙 S))
      (prod.lift (prod.fst ≫ f) (prod.snd ≫ g)) := by
  refine ⟨⟨by ext <;> simp [pullback.condition]⟩,
    ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift (c.snd ≫ prod.fst) (c.snd ≫ prod.snd) ?_
    have h₁ : c.snd ≫ prod.fst ≫ f = c.fst := by
      simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using
        (congrArg (fun z => z ≫ prod.fst) c.condition).symm
    have h₂ : c.snd ≫ prod.snd ≫ g = c.fst := by
      simpa only [Category.assoc, prod.lift_snd, Category.comp_id] using
        (congrArg (fun z => z ≫ prod.snd) c.condition).symm
    calc
      _ = c.fst := (Category.assoc _ _ _).trans h₁
      _ = _ := h₂.symm.trans (Category.assoc _ _ _).symm
  · intro c
    have h₁ : c.snd ≫ prod.fst ≫ f = c.fst := by
      simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using
        (congrArg (fun z => z ≫ prod.fst) c.condition).symm
    rw [pullback.lift_fst_assoc]
    exact (Category.assoc _ _ _).trans h₁
  · intro c
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, pullback.lift_fst]
    · simp only [Category.assoc, prod.lift_snd, pullback.lift_snd]
  · intro c m _ hn
    apply pullback.hom_ext
    · have h := congrArg (fun z => z ≫ prod.fst) hn
      rw [pullback.lift_fst]
      simpa only [Category.assoc, prod.lift_fst] using h
    · have h := congrArg (fun z => z ≫ prod.snd) hn
      rw [pullback.lift_snd]
      simpa only [Category.assoc, prod.lift_snd] using h

/-- Over a separated base, a fibre product is a closed subscheme of the
ordinary product of its two factors. -/
instance pullbackToProd_isClosedImmersion [S.IsSeparated] :
    IsClosedImmersion
      (prod.lift (pullback.fst f g) (pullback.snd f g)) := by
  exact MorphismProperty.of_isPullback
    (isPullback_pullbackToProd_diagonal f g) inferInstance

/-- Taking the product with the identity preserves a closed immersion. -/
theorem isClosedImmersion_prodMap_id {A B Z : Scheme.{u}}
    (j : A ⟶ B) [IsClosedImmersion j] :
    IsClosedImmersion (prod.map j (𝟙 Z)) := by
  let e := pullbackProdFstIsoProd j Z
  have he : e.inv ≫ pullback.snd j (prod.fst : B ⨯ Z ⟶ B) =
      prod.map j (𝟙 Z) := by
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.map_fst] using
        pullbackProdFstIsoProd_inv_snd_fst j Z
    · simpa only [Category.assoc, prod.map_snd, Category.comp_id] using
        pullbackProdFstIsoProd_inv_snd_snd j Z
  rw [← he]
  infer_instance

end PfaffianDescent

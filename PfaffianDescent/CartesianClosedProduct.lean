import PfaffianDescent.PullbackToProductClosedImmersion

/-!
# Closed immersions into ordinary products from Cartesian squares

A closed subscheme of a base-changed space embeds in the ordinary product
of the original space and the new base whenever the original base is
separated.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {Z X Y : Scheme.{u}}

/-- Taking the product with an identity gives the pullback of the second
projection along any map. -/
theorem isPullback_prodMap_id_snd (f : X ⟶ Y) :
    IsPullback (prod.map (𝟙 Z) f) prod.snd prod.snd f := by
  let e := pullbackProdSndIsoProd f Z
  apply IsPullback.of_iso_pullback ⟨by simp [prod.map_snd]⟩ e.symm
  · apply prod.hom_ext
    · simpa only [e, Iso.symm_hom, Category.assoc, prod.map_fst, Category.comp_id] using
        pullbackProdSndIsoProd_inv_fst_fst f Z
    · simpa only [e, Iso.symm_hom, Category.assoc, prod.map_snd] using
        pullbackProdSndIsoProd_inv_fst_snd f Z
  · simpa only [e, Iso.symm_hom] using pullbackProdSndIsoProd_inv_snd f Z

/-- A product with an identity preserves an open immersion in the second
factor. -/
theorem isOpenImmersion_prodMap_id_snd (f : X ⟶ Y) [IsOpenImmersion f] :
    IsOpenImmersion (prod.map (𝟙 Z) f) :=
  MorphismProperty.of_isPullback (isPullback_prodMap_id_snd (Z := Z) f).flip inferInstance

variable {A B S T H : Scheme.{u}}
  (f : B ⟶ A) (g : B ⟶ T) (p : A ⟶ S) (q : T ⟶ S)
  (h : IsPullback f g p q) (i : H ⟶ B)

include h in
/-- A closed subscheme of a Cartesian base change is closed in the ordinary
product over a separated base. -/
theorem isClosedImmersion_prodLift_of_isPullback [S.IsSeparated]
    [IsClosedImmersion i] :
    IsClosedImmersion (prod.lift (i ≫ f) (i ≫ g)) := by
  let e := h.isoPullback
  have h₁ : IsClosedImmersion (i ≫ e.hom) := by
    exact @IsClosedImmersion.comp _ _ _ i e.hom inferInstance (by infer_instance)
  have h₂ : IsClosedImmersion
      (prod.lift (pullback.fst p q) (pullback.snd p q)) := by
    infer_instance
  have heq : prod.lift (i ≫ f) (i ≫ g) =
      (i ≫ e.hom) ≫ prod.lift (pullback.fst p q) (pullback.snd p q) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst]
      change i ≫ f = i ≫ (h.isoPullback.hom ≫ pullback.fst p q)
      exact congrArg (fun z => i ≫ z) h.isoPullback_hom_fst.symm
    · simp only [Category.assoc, prod.lift_snd]
      change i ≫ g = i ≫ (h.isoPullback.hom ≫ pullback.snd p q)
      exact congrArg (fun z => i ≫ z) h.isoPullback_hom_snd.symm
  rw [heq]
  exact @IsClosedImmersion.comp _ _ _ (i ≫ e.hom)
    (prod.lift (pullback.fst p q) (pullback.snd p q)) h₁ h₂

end PfaffianDescent

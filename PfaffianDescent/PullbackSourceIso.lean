import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Replacing both factors of a fibre product by isomorphic schemes

This form keeps the two comparison maps explicit, so it can be used when
replacing universal-family fibres with concrete hypersurfaces.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits

universe u

variable {C : Type u} [Category C] [HasPullbacks C]
  {X X' Y Y' Z : C} (eX : X ≅ X') (eY : Y ≅ Y')
  (f : X' ⟶ Z) (g : Y' ⟶ Z)

/-- A fibre product is unchanged when both factors are replaced by
isomorphic objects with the corresponding maps. -/
noncomputable def pullbackSourceIso :
    pullback (eX.hom ≫ f) (eY.hom ≫ g) ≅ pullback f g :=
  asIso (pullback.map (eX.hom ≫ f) (eY.hom ≫ g) f g
    eX.hom eY.hom (𝟙 Z) (by simp) (by simp))

/-- The comparison projects to the first chosen isomorphism. -/
theorem pullbackSourceIso_hom_fst :
    (pullbackSourceIso eX eY f g).hom ≫ pullback.fst f g =
      pullback.fst (eX.hom ≫ f) (eY.hom ≫ g) ≫ eX.hom := by
  simp only [pullbackSourceIso, asIso_hom, pullback.map, pullback.lift_fst]

/-- The comparison projects to the second chosen isomorphism. -/
theorem pullbackSourceIso_hom_snd :
    (pullbackSourceIso eX eY f g).hom ≫ pullback.snd f g =
      pullback.snd (eX.hom ≫ f) (eY.hom ≫ g) ≫ eY.hom := by
  simp only [pullbackSourceIso, asIso_hom, pullback.map, pullback.lift_snd]

/-- Transport an intersection through two source isomorphisms after proving
that each square has the required map to the common target. -/
noncomputable def pullbackTransportIso
    (f₀ : X ⟶ Z) (g₀ : Y ⟶ Z)
    (hf : f₀ = eX.hom ≫ f) (hg : g₀ = eY.hom ≫ g) :
    pullback f₀ g₀ ≅ pullback f g :=
  pullback.congrHom hf hg ≪≫ pullbackSourceIso eX eY f g

/-- Transport of a fibre product preserves its second projection, up to
the selected isomorphism of the second source. -/
theorem pullbackTransportIso_hom_snd
    (f₀ : X ⟶ Z) (g₀ : Y ⟶ Z)
    (hf : f₀ = eX.hom ≫ f) (hg : g₀ = eY.hom ≫ g) :
    (pullbackTransportIso eX eY f g f₀ g₀ hf hg).hom ≫
      pullback.snd f g = pullback.snd f₀ g₀ ≫ eY.hom := by
  subst f₀
  subst g₀
  simp [pullbackTransportIso, pullbackSourceIso, pullback.congrHom,
    pullback.map, pullback.lift_snd]

/-- Transport of a fibre product preserves its first projection, up to
the selected isomorphism of the first source. -/
theorem pullbackTransportIso_hom_fst
    (f₀ : X ⟶ Z) (g₀ : Y ⟶ Z)
    (hf : f₀ = eX.hom ≫ f) (hg : g₀ = eY.hom ≫ g) :
    (pullbackTransportIso eX eY f g f₀ g₀ hf hg).hom ≫
      pullback.fst f g = pullback.fst f₀ g₀ ≫ eX.hom := by
  subst f₀
  subst g₀
  simp [pullbackTransportIso, pullbackSourceIso, pullback.congrHom,
    pullback.map, pullback.lift_fst]

end PfaffianDescent

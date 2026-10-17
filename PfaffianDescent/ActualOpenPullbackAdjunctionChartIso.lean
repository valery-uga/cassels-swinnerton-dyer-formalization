import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Unique

/- SOURCE ONLY / UNVERIFIED. Actual open pullback adjunct equals literal
restriction adjunct, with its chart-section isomorphism derived internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

lemma actualOpenPullbackAdjunction_homEquiv_restriction
    {Y X : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
    (M : X.Modules) (N : Y.Modules) (a : (Scheme.Modules.pullback i).obj M ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv M N a =
      (Scheme.Modules.restrictAdjunction i).homEquiv M N
        ((Scheme.Modules.restrictFunctorIsoPullback i).hom.app M ≫ a) := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc]
  change _ = ((Scheme.Modules.restrictAdjunction i).unit.app M ≫
    (Scheme.Modules.pushforward i).map
      (((Scheme.Modules.restrictAdjunction i).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction i)).hom.app M)) ≫ _
  rw [Adjunction.unit_leftAdjointUniq_hom_app]

/-- The adjunct of an ACTUAL chart-source Iso is an Iso on sections over
the open image of that chart. No desired restriction square is input. -/
theorem actualOpenPullbackAdjunction_chartIso_app_isIso
    {Y X : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
    (M : X.Modules) (N : Y.Modules) (e : (Scheme.Modules.pullback i).obj M ≅ N) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv M N e.hom).app
      (i ''ᵁ ⊤)) := by
  let V := i ''ᵁ ⊤
  let b := (Scheme.Modules.restrictFunctorIsoPullback i).hom.app M ≫ e.hom
  letI : IsIso b := by dsimp only [b]; infer_instance
  have hV : i ''ᵁ (i ⁻¹ᵁ V) = V := by rw [i.preimage_image_eq]
  letI : IsIso (((Scheme.Modules.restrictAdjunction i).unit.app M).app V) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have he : homOfLE (i.image_preimage_le V) = eqToHom hV := Subsingleton.elim _ _
    rw [he]
    change IsIso (M.presheaf.mapIso (eqToIso hV).op).hom
    exact (M.presheaf.mapIso (eqToIso hV).op).isIso_hom
  rw [actualOpenPullbackAdjunction_homEquiv_restriction, Adjunction.homEquiv_unit,
    Scheme.Modules.Hom.comp_app]
  change IsIso ((((Scheme.Modules.restrictAdjunction i).unit.app M).app V) ≫
    (((Scheme.Modules.pushforward i).map b).app V))
  infer_instance

end PfaffianDescent

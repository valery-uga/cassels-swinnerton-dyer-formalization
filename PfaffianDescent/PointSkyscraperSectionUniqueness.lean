import PfaffianDescent.PointSkyscraperGlobalSection

/-!
# Uniqueness of global point sections from a neighborhood

Restriction to an open containing the center is injective for a skyscraper,
and this property transports to the actual point quotient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
theorem schemeModuleSkyscraper_restriction_from_top_injective
    {X : Scheme.{u}} (x : X) (A : ModuleCat.{u} (X.presheaf.stalk x))
    (U : X.Opens) (hx : x ∈ U) :
    Function.Injective ((schemeModuleSkyscraper x A).val.map
      (homOfLE (le_top : U ≤ ⊤)).op) := by
  intro a b hab
  apply (schemeModuleSkyscraperAbPresheafAddEquivOfMem x A ⊤
    (show x ∈ ⊤ from trivial)).injective
  have h := congrArg (schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx) hab
  change schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
      ((schemeModuleSkyscraperAbPresheaf x A).map
        (homOfLE (le_top : U ≤ ⊤)).op a) =
    schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
      ((schemeModuleSkyscraperAbPresheaf x A).map
        (homOfLE (le_top : U ≤ ⊤)).op b) at h
  rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_map,
    schemeModuleSkyscraperAbPresheafAddEquivOfMem_map] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem schemeModule_restriction_from_top_injective_of_skyscraperIso
    {X : Scheme.{u}} (x : X) (A : ModuleCat.{u} (X.presheaf.stalk x))
    (M : X.Modules) (e : M ≅ schemeModuleSkyscraper x A)
    (U : X.Opens) (hx : x ∈ U) :
    Function.Injective (M.val.map (homOfLE (le_top : U ≤ ⊤)).op) := by
  intro a b hab
  have h := congrArg (fun t ↦ e.hom.val.app (op U) t) hab
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply] at h
  have ht := schemeModuleSkyscraper_restriction_from_top_injective x A U hx h
  have hc := congrArg (fun t ↦ e.inv.val.app (op (⊤ : X.Opens)) t) ht
  change (e.hom ≫ e.inv).val.app (op (⊤ : X.Opens)) a =
    (e.hom ≫ e.inv).val.app (op (⊤ : X.Opens)) b at hc
  rw [e.hom_inv_id] at hc
  exact hc

end PfaffianDescent

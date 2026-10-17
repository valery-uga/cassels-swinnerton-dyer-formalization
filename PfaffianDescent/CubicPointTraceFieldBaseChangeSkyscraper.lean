import PfaffianDescent.SchemeModuleSkyscraper
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Actual pushforward of a scheme-module skyscraper

The scalar restriction is the actual map on local rings. This comparison
provides the right-adjoint square used to compute stalks of actual pullback.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
  (A : ModuleCat.{u} (X.presheaf.stalk x))

private theorem cubicPointTraceFieldBaseChange_skyscraper_scalar
    (U : Y.Opens) (r : Γ(Y, U))
    (m : (((Scheme.Modules.pushforward f).obj (schemeModuleSkyscraper x A)).val.obj (op U))) :
    ((𝟙 (schemeModuleSkyscraperAbPresheaf (f x)
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A))).app (op U))
        (r • m) =
      r • ((𝟙 (schemeModuleSkyscraperAbPresheaf (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A))).app (op U)) m := by
  by_cases hx : f x ∈ U
  · apply (schemeModuleSkyscraperAbPresheafAddEquivOfMem (f x)
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A) U hx).injective
    letI := schemeModuleSkyscraperAbPresheaf_module x A (op (f ⁻¹ᵁ U))
    let m' : (schemeModuleSkyscraperAbPresheaf x A).obj (op (f ⁻¹ᵁ U)) := m
    rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul]
    change schemeModuleSkyscraperAbPresheafAddEquivOfMem x A (f ⁻¹ᵁ U) hx
        ((f.app U).hom r • m') =
      (f.stalkMap x).hom (Y.presheaf.germ U (f x) hx r) •
        schemeModuleSkyscraperAbPresheafAddEquivOfMem x A (f ⁻¹ᵁ U) hx m'
    rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_smul,
      f.germ_stalkMap_apply U x hx r]
  · have hz : IsZero ((schemeModuleSkyscraperAbPresheaf (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A)).obj (op U)) := by
      have ht : IsZero (⊤_ AddCommGrpCat.{u}) :=
        (isZero_zero AddCommGrpCat.{u}).of_iso
          ((isZero_zero AddCommGrpCat.{u}).isoIsTerminal terminalIsTerminal).symm
      exact ht.of_iso (eqToIso (by
        simp [schemeModuleSkyscraperAbPresheaf, hx]))
    exact @Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero hz) _ _

/-- Pushing a skyscraper along a scheme morphism restricts its stalk-module
action by the actual local-ring map, and moves its support to the image point. -/
def cubicPointTraceFieldBaseChangeSkyscraperPushforwardIso :
    (Scheme.Modules.pushforward f).obj (schemeModuleSkyscraper x A) ≅
      schemeModuleSkyscraper (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A) where
  hom := {
    val := PresheafOfModules.homMk
      (𝟙 (schemeModuleSkyscraperAbPresheaf (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A)))
      (fun U r m => cubicPointTraceFieldBaseChange_skyscraper_scalar f x A U.unop r m) }
  inv := {
    val := PresheafOfModules.homMk
      (𝟙 (schemeModuleSkyscraperAbPresheaf (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj A)))
      (fun U r m => (cubicPointTraceFieldBaseChange_skyscraper_scalar f x A U.unop r m).symm) }
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    rfl
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    rfl

/-- The actual skyscraper-pushforward comparison is natural in the local
module; no choices of stalk coordinates enter its definition. -/
def cubicPointTraceFieldBaseChangeSkyscraperPushforwardNatIso :
    schemeModuleSkyscraperFunctor X x ⋙ Scheme.Modules.pushforward f ≅
      ModuleCat.restrictScalars (f.stalkMap x).hom ⋙
        schemeModuleSkyscraperFunctor Y (f x) :=
  NatIso.ofComponents (fun A => cubicPointTraceFieldBaseChangeSkyscraperPushforwardIso f x A)
    (fun φ => by
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      rfl)

end
end PfaffianDescent

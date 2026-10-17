import PfaffianDescent.ClosedImmersionPushforwardExact
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # The actual pushforward-stalk map respects the scheme stalk-ring map -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false in
theorem pointCartierNativeStalkPushforward_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (M : X.Modules) :
    letI : Module (Y.presheaf.stalk (f x))
      (((Scheme.Modules.pushforward f).obj M).presheaf.stalk (f x)) :=
        schemeModuleStalkModule _ _
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) := schemeModuleStalkModule _ _
    ∀ (r : Y.presheaf.stalk (f x))
      (m : ((Scheme.Modules.pushforward f).obj M).presheaf.stalk (f x)),
      M.presheaf.stalkPushforward AddCommGrpCat f.base x (r • m) =
        f.stalkMap x r • M.presheaf.stalkPushforward AddCommGrpCat f.base x m := by
  dsimp only
  letI := schemeModuleStalkModule ((Scheme.Modules.pushforward f).obj M) (f x)
  letI := schemeModuleStalkModule M x
  intro r m
  let N := (Scheme.Modules.pushforward f).obj M
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq N.presheaf m
  obtain ⟨V, hVU, hxV, a, rfl⟩ := Y.presheaf.exists_le_germ_eq r hxU
  let sV := N.presheaf.map (homOfLE hVU).op s
  have hgs : N.presheaf.germ V (f x) hxV sV = N.presheaf.germ U (f x) hxU s :=
    N.presheaf.germ_res_apply (homOfLE hVU) (f x) hxV s
  rw [← hgs]
  erw [← PresheafOfModules.germ_smul N.val (f x) V hxV a sV]
  have hl := TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat f.base
    M.presheaf V x hxV (a • sV)
  have hr := TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat f.base
    M.presheaf V x hxV sV
  erw [hl, hr]
  rw [Scheme.Hom.germ_stalkMap_apply]
  let tV : Γ(M, f ⁻¹ᵁ V) := sV
  change M.presheaf.germ (f ⁻¹ᵁ V) x hxV (f.app V a • tV) =
    X.presheaf.germ (f ⁻¹ᵁ V) x hxV (f.app V a) • M.presheaf.germ (f ⁻¹ᵁ V) x hxV tV
  exact PresheafOfModules.germ_smul M.val x (f ⁻¹ᵁ V) hxV (f.app V a) tV

end PfaffianDescent

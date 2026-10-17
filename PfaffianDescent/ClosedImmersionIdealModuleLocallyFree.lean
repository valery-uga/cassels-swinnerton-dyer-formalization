import PfaffianDescent.ClosedImmersionIdealModuleAffineFree
import PfaffianDescent.SheafFreeCover
import PfaffianDescent.VoisinPositiveTwistTriviality

/-! Local freeness of the actual ideal module on regular-principal charts. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

theorem RegularPrincipalImmersion.closedImmersionModule_isLocallyFree
    {X Z : Scheme.{u}} {f : Z ⟶ X} [IsClosedImmersion f]
    (H : RegularPrincipalImmersion f) :
    (IdealSheafDataModule.closedImmersionModule f).IsLocallyFree := by
  let M : X.Modules := IdealSheafDataModule.closedImmersionModule f
  let C : H.Index → X.affineOpens := fun j => by
    letI : IsOpenImmersion (H.target j) := H.targetOpen j
    let W : (Spec (H.A j)).affineOpens :=
      ⟨⊤, isAffineOpen_top (Spec (H.A j))⟩
    exact ⟨H.target j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩
  have hcover : (Opens.grothendieckTopology X).CoversTop
      (fun j : H.Index => (C j).1) := by
    convert H.targetAffineOpens_coversTop using 1
    funext j
    letI : IsOpenImmersion (H.target j) := H.targetOpen j
    change H.target j ''ᵁ ⊤ = (H.target j).opensRange
    exact Scheme.Hom.image_top_eq_opensRange (H.target j)
  apply sheaf_isLocallyFree_of_coverIso X.ringCatSheaf M
    (fun j : H.Index => (C j).1) hcover
    (fun _ => PUnit.{u+1})
  intro j
  letI : IsOpenImmersion (H.target j) := H.targetOpen j
  letI : IsIso (H.chartIdealModuleHom j) := H.chartIdealModuleHom_isIso j
  let U : X.Opens := (C j).1
  let e₀ : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ≅ M.restrict U.ι :=
    asIso (H.chartIdealModuleHom j)
  let e₁ := ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U e₀.symm
  exact (coproductUniqueIso (fun _ : PUnit.{u+1} =>
      SheafOfModules.unit (X.ringCatSheaf.over U))) ≪≫ e₁.symm

end PfaffianDescent

import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits
universe u v w
section
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] [HasBinaryProducts C]

/-- A sheaf isomorphic to a free sheaf is locally free. -/
lemma sheaf_isLocallyFree_of_freeIso (M : SheafOfModules R) (I : Type u)
    (e : SheafOfModules.free I ≅ M) : M.IsLocallyFree := by
  let G : M.GeneratingSections :=
    { I := I
      s := M.freeHomEquiv e.hom
      epi := by rw [Equiv.symm_apply_apply]; infer_instance }
  haveI : IsIso G.π := by
    change IsIso (M.freeHomEquiv.symm (M.freeHomEquiv e.hom))
    rw [Equiv.symm_apply_apply]
    infer_instance
  haveI : G.localGeneratorsData.IsLocallyFreeData := by
    refine { isIso := fun (U : C) => ?_ }
    let F : SheafOfModules R ⥤ SheafOfModules (R.over U) :=
      SheafOfModules.pushforward (F := Over.forget U) (𝟙 (R.over U))
    let η : SheafOfModules.unit (R.over U) ≅ F.obj (SheafOfModules.unit R) := Iso.refl _
    haveI : PreservesColimitsOfSize.{u, u} F := by dsimp [F]; infer_instance
    change IsIso (G.map F η).π
    infer_instance
  exact G.localGeneratorsData.isLocallyFree

end
end PfaffianDescent

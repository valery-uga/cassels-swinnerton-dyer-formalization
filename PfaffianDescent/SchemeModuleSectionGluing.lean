import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u v
section
variable {X : Scheme.{u}} (M : X.Modules) {ι : Type v}
    (U : X.Opens) (V : ι → X.Opens) (hV : ∀ i, V i ≤ U) (hcover : U ≤ ⨆ i, V i)

include hcover

/-- Compatible module-sheaf sections on an open cover glue uniquely in the original section module. -/
theorem schemeModuleSections_glue (s : ∀ i, Γ(M, V i))
    (h : ∀ i j, M.val.map (homOfLE (show V i ⊓ V j ≤ V i from inf_le_left)).op (s i) =
      M.val.map (homOfLE (show V i ⊓ V j ≤ V j from inf_le_right)).op (s j)) :
    ∃! x : Γ(M, U), ∀ i, M.val.map (homOfLE (hV i)).op x = s i := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  exact F.existsUnique_gluing' V U (fun i => homOfLE (hV i)) hcover s h

/-- Sections of an actual module sheaf are determined on an open cover. -/
lemma schemeModuleSections_ext (x y : Γ(M, U))
    (h : ∀ i, M.val.map (homOfLE (hV i)).op x = M.val.map (homOfLE (hV i)).op y) : x = y := by
  let s := fun i => M.val.map (homOfLE (hV i)).op x
  have hs : ∀ i j, M.val.map (homOfLE (show V i ⊓ V j ≤ V i from inf_le_left)).op (s i) =
      M.val.map (homOfLE (show V i ⊓ V j ≤ V j from inf_le_right)).op (s j) := by
    intro i j
    exact (PresheafOfModules.map_comp_apply M.val (homOfLE (hV i)).op (homOfLE inf_le_left).op x).symm.trans
      (PresheafOfModules.map_comp_apply M.val (homOfLE (hV j)).op (homOfLE inf_le_right).op x)
  obtain ⟨z, hz, hu⟩ := schemeModuleSections_glue M U V hV hcover s hs
  exact (hu x (fun _ => rfl)).trans (hu y (fun i => (h i).symm)).symm

end
end PfaffianDescent

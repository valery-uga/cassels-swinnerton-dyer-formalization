import PfaffianDescent.VoisinSheafStalk
import PfaffianDescent.SchemeModuleSectionOnOpen

/-! # Actual affine local lifts of the unit section -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- A sheaf epimorphism to the unit module has an actual section lifting
`1` on an affine neighborhood of every point.  This is proved from germs and
their finite equality neighborhood, without a quasicoherence assumption. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_affine_unit_lift
    {X : Scheme.{u}} (M : X.Modules)
    (p : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Epi p] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      ∃ t : M.presheaf.obj (Opposite.op U),
        p.val.app (Opposite.op U) t = (1 : Γ(X, U)) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hsurj := schemeModule_epi_stalkMap_surjective p x
  obtain ⟨m, hm⟩ := hsurj (O.presheaf.germ ⊤ x trivial (1 : Γ(X, ⊤)))
  obtain ⟨U, hxU, s, hms⟩ := M.presheaf.exists_germ_eq m
  have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := AddCommGrpCat) U x hxU ((Scheme.Modules.toPresheaf X).map p) s
  have heq : O.presheaf.germ U x hxU (p.val.app (Opposite.op U) s) =
      O.presheaf.germ ⊤ x trivial (1 : Γ(X, ⊤)) := by
    change schemeModuleStalkLinearMap p x (M.presheaf.germ U x hxU s) =
      O.presheaf.germ U x hxU (p.val.app (Opposite.op U) s) at hg
    exact hg.symm.trans (hms ▸ hm)
  obtain ⟨V, hxV, iVU, iVtop, hV⟩ :=
    O.presheaf.germ_eq (U := U) (V := ⊤) x hxU trivial _ _ heq
  let t := M.presheaf.map iVU.op s
  have ht : p.val.app (Opposite.op V) t = (1 : Γ(X, V)) := by
    have hn := PresheafOfModules.naturality_apply p.val iVU.op s
    change p.val.app (Opposite.op V) t =
      O.presheaf.map iVU.op (p.val.app (Opposite.op U) s) at hn
    exact hn.trans (hV.trans (map_one (X.presheaf.map iVtop.op).hom))
  obtain ⟨W, hWaff, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  refine ⟨W, hxW, hWaff, M.presheaf.map (homOfLE hWV).op t, ?_⟩
  have hn := PresheafOfModules.naturality_apply p.val (homOfLE hWV).op t
  change p.val.app (Opposite.op W) (M.presheaf.map (homOfLE hWV).op t) =
    O.presheaf.map (homOfLE hWV).op (p.val.app (Opposite.op V) t) at hn
  exact hn.trans (by rw [ht]; exact map_one (X.presheaf.map (homOfLE hWV).op).hom)

end PfaffianDescent

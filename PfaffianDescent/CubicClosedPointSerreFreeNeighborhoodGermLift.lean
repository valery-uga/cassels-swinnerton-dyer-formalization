import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodLift

/-! # Extending a prescribed actual stalk lift to an affine neighborhood -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- A prescribed compatible actual stalk lift extends to a section lift on
an affine subneighborhood, preserving its original germ. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_affine_lift_of_germ
    {X : Scheme.{u}} (M N : X.Modules) (p : M ⟶ N)
    (O : X.Opens) (x : X) (hxO : x ∈ O)
    (t : N.presheaf.obj (Opposite.op O)) (m : M.presheaf.stalk x)
    (hm : schemeModuleStalkLinearMap p x m = N.presheaf.germ O x hxO t) :
    ∃ (V : X.Opens) (hxV : x ∈ V), IsAffineOpen V ∧
      ∃ (hVO : V ≤ O) (s : M.presheaf.obj (Opposite.op V)),
        M.presheaf.germ V x hxV s = m ∧
        p.val.app (Opposite.op V) s = N.presheaf.map (homOfLE hVO).op t := by
  obtain ⟨U, hxU, s, hms⟩ := M.presheaf.exists_germ_eq m
  have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := AddCommGrpCat) U x hxU ((Scheme.Modules.toPresheaf X).map p) s
  have heq : N.presheaf.germ U x hxU (p.val.app (Opposite.op U) s) =
      N.presheaf.germ O x hxO t := by
    change schemeModuleStalkLinearMap p x (M.presheaf.germ U x hxU s) =
      N.presheaf.germ U x hxU (p.val.app (Opposite.op U) s) at hg
    exact hg.symm.trans (hms ▸ hm)
  obtain ⟨W, hxW, iWU, iWO, hW⟩ :=
    N.presheaf.germ_eq (U := U) (V := O) x hxU hxO _ _ heq
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
  have hVU : V ≤ U := hVW.trans (leOfHom iWU)
  have hVO : V ≤ O := hVW.trans (leOfHom iWO)
  refine ⟨V, hxV, hV, hVO, M.presheaf.map (homOfLE hVU).op s, ?_, ?_⟩
  · exact (M.presheaf.germ_res_apply (homOfLE hVU) x hxV s).trans hms
  · have hn := PresheafOfModules.naturality_apply p.val (homOfLE hVU).op s
    change p.val.app (Opposite.op V) (M.presheaf.map (homOfLE hVU).op s) =
      N.presheaf.map (homOfLE hVU).op (p.val.app (Opposite.op U) s) at hn
    refine hn.trans ?_
    have hw' := congrArg (N.presheaf.map (homOfLE hVW).op) hW
    have hWU : iWU = homOfLE (leOfHom iWU) := Subsingleton.elim _ _
    have hWO : iWO = homOfLE (leOfHom iWO) := Subsingleton.elim _ _
    rw [hWU, hWO] at hw'
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hw'
    have hcompU : (homOfLE (leOfHom iWU)).op ≫ (homOfLE hVW).op =
        (homOfLE hVU).op := Subsingleton.elim _ _
    have hcompO : (homOfLE (leOfHom iWO)).op ≫ (homOfLE hVW).op =
        (homOfLE hVO).op := Subsingleton.elim _ _
    rw [hcompU, hcompO] at hw'
    exact hw'

end PfaffianDescent

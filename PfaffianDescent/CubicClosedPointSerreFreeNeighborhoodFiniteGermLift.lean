import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodGermLift
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodLocalStalk

/-! # Simultaneous actual lifts of finitely many native stalk generators -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u v
set_option backward.isDefEq.respectTransparency false

/-- The actual native stalk map from the unit sends one to the actual
germ of the value of one. -/
theorem cubicClosedPointSerreFreeNeighborhood_unit_hom_stalk_one
    {X : Scheme.{u}} (N : X.Modules)
    (p : SheafOfModules.unit X.ringCatSheaf ⟶ N) (x : X) :
    (schemeModuleStalkModuleFunctor X x).map p ((schemeModuleUnitStalkIso X x).inv 1) =
      N.presheaf.germ ⊤ x trivial (p.val.app (Opposite.op ⊤) (1 : Γ(X, ⊤))) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hunit : (schemeModuleUnitStalkIso X x).inv 1 =
      O.presheaf.germ ⊤ x trivial (1 : Γ(X, ⊤)) := by
    have h := presheafOfModules_unitStalkAddEquiv_germ X.presheaf x ⊤ trivial (1 : Γ(X, ⊤))
    rw [map_one] at h
    exact h
  rw [hunit]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := AddCommGrpCat.{u}) ⊤ x trivial ((Scheme.Modules.toPresheaf X).map p) (1 : Γ(X, ⊤))

/-- A finite family of prescribed compatible native stalk lifts extends
simultaneously to actual section lifts on one affine neighborhood. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_affine_lift_family_of_germ
    {X : Scheme.{u}} (M N : X.Modules) (p : M ⟶ N) (x : X)
    {J : Type v} [Finite J]
    (t : J → Γ(N, ⊤)) (m : J → M.presheaf.stalk x)
    (hm : ∀ j, schemeModuleStalkLinearMap p x (m j) = N.presheaf.germ ⊤ x trivial (t j)) :
    ∃ (U : X.Opens) (hxU : x ∈ U), IsAffineOpen U ∧
      ∃ s : J → Γ(M, U), ∀ j,
        M.presheaf.germ U x hxU (s j) = m j ∧
        p.val.app (Opposite.op U) (s j) =
          N.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (t j) := by
  classical
  choose U hxU hU hUt s hs hp using
    (fun j => cubicClosedPointSerreFreeNeighborhood_exists_affine_lift_of_germ
      M N p ⊤ x trivial (t j) (m j) (hm j))
  have hxW : x ∈ ⨅ j, U j := by
    change x ∈ ((⨅ j, U j : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxU
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
  let hVU : ∀ j, V ≤ U j := fun j => hVW.trans (iInf_le U j)
  let sV : J → Γ(M, V) := fun j => M.presheaf.map (homOfLE (hVU j)).op (s j)
  refine ⟨V, hxV, hV, sV, ?_⟩
  intro j
  refine ⟨(M.presheaf.germ_res_apply (homOfLE (hVU j)) x hxV (s j)).trans (hs j), ?_⟩
  have hn := PresheafOfModules.naturality_apply p.val (homOfLE (hVU j)).op (s j)
  change p.val.app (Opposite.op V) (sV j) =
    N.presheaf.map (homOfLE (hVU j)).op (p.val.app (Opposite.op (U j)) (s j)) at hn
  rw [hp j] at hn
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hn
  have hc : (homOfLE (hUt j)).op ≫ (homOfLE (hVU j)).op =
      (homOfLE (show V ≤ ⊤ from le_top)).op := Subsingleton.elim _ _
  rw [hc] at hn
  exact hn

end PfaffianDescent

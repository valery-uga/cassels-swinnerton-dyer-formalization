import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodFiniteGermLift

/-! # Lifting actual finite-free native stalk morphisms to neighborhoods -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- A native stalk map from the actual free rank-two sheaf, compatible with
an actual quotient map, extends to an actual quotient-compatible map on an
affine neighborhood. Its native ambient stalk map is proved to be the
original prescribed map. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_free_lift_of_stalk
    {X : Scheme.{u}} (E M : X.Modules) (p : E ⟶ M)
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ⟶ M)
    (x : X)
    (l : (schemeModuleStalkModuleFunctor X x).obj
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) ⟶
      (schemeModuleStalkModuleFunctor X x).obj E)
    (hl : l ≫ (schemeModuleStalkModuleFunctor X x).map p =
      (schemeModuleStalkModuleFunctor X x).map q) :
    ∃ (U : X.Opens) (hxU : x ∈ U), IsAffineOpen U ∧
      ∃ v : (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))).restrict U.ι ⟶
          E.restrict U.ι,
        v ≫ (Scheme.Modules.restrictFunctor U.ι).map p =
          (Scheme.Modules.restrictFunctor U.ι).map q ∧
        cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U ⟨x, hxU⟩ _ E v = l := by
  let I := ULift.{u} (Fin 2)
  let B : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) I
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let F := schemeModuleStalkModuleFunctor X x
  letI : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  let k : I → (O ⟶ B) := fun j => SheafOfModules.ιFree j
  let a := schemeModuleUnitStalkIso X x
  let m : I → E.presheaf.stalk x := fun j => l (F.map (k j) (a.inv 1))
  let t : I → Γ(M, ⊤) := fun j => (k j ≫ q).val.app (Opposite.op ⊤) (1 : Γ(X, ⊤))
  have hm : ∀ j, schemeModuleStalkLinearMap p x (m j) = M.presheaf.germ ⊤ x trivial (t j) := by
    intro j
    have h := congrArg (fun f => f.hom (F.map (k j) (a.inv 1))) hl
    change F.map p (m j) = F.map q (F.map (k j) (a.inv 1)) at h
    have hc := congrArg (fun f => f.hom (a.inv 1)) (F.map_comp (k j) q)
    exact h.trans (hc.symm.trans (cubicClosedPointSerreFreeNeighborhood_unit_hom_stalk_one M (k j ≫ q) x))
  obtain ⟨U, hxU, hU, s, hs⟩ :=
    cubicClosedPointSerreFreeNeighborhood_exists_affine_lift_family_of_germ E M p x t m hm
  let R := Scheme.Modules.restrictFunctor U.ι
  letI : R.IsLeftAdjoint := by dsimp [R]; infer_instance
  let u := Scheme.Modules.restrictUnitIso U.ι
  let z := SheafOfModules.mapFreeIso R I u.symm
  let v₀ : SheafOfModules.free (R := (U : Scheme).ringCatSheaf) I ⟶ E.restrict U.ι :=
    Sigma.desc (fun j => schemeModuleSectionOnOpenHom E U (s j))
  let v : B.restrict U.ι ⟶ E.restrict U.ι := z.inv ≫ v₀
  have hvj : ∀ j, R.map (k j) ≫ v = u.hom ≫ schemeModuleSectionOnOpenHom E U (s j) := by
    intro j
    change R.map (SheafOfModules.ιFree j) ≫ (z.inv ≫ v₀) = _
    rw [← Category.assoc, SheafOfModules.map_ιFree_mapFreeIso_inv]
    change (u.hom ≫ SheafOfModules.ιFree j) ≫ v₀ = _
    rw [Category.assoc]
    congr 1
    exact Sigma.ι_desc (fun j => schemeModuleSectionOnOpenHom E U (s j)) j
  have hv : v ≫ R.map p = R.map q := by
    apply (isColimitOfPreserves R (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)).hom_ext
    intro j
    change R.map (k j.as) ≫ (v ≫ R.map p) = R.map (k j.as) ≫ R.map q
    rw [← Category.assoc, hvj, Category.assoc,
      cubicClosedPointSerreFreeNeighborhood_section_naturality]
    have ht : p.val.app (Opposite.op U) (s j.as) =
        (k j.as ≫ q).val.app (Opposite.op U) (1 : Γ(X, U)) := by
      exact (hs j.as).2.trans (schemeModuleUnitHom_restrict_one M (k j.as ≫ q) U).symm
    rw [ht, cubicClosedPointSerreFreeNeighborhood_section_of_unit_hom]
    change (u.hom ≫ u.inv) ≫ R.map (k j.as ≫ q) = R.map (k j.as) ≫ R.map q
    rw [u.hom_inv_id, Category.id_comp, R.map_comp]
  have hvl : cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U ⟨x, hxU⟩ B E v = l := by
    apply (isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)).hom_ext
    intro j
    change F.map (k j.as) ≫ _ = F.map (k j.as) ≫ l
    have hc := cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_comp U ⟨x, hxU⟩ O B E
      (R.map (k j.as)) v
    rw [cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_restrict] at hc
    change cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U ⟨x, hxU⟩ O E
        (R.map (k j.as) ≫ v) =
      F.map (k j.as) ≫ cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U ⟨x, hxU⟩ B E v at hc
    rw [← hc, hvj]
    apply (cancel_epi a.inv).mp
    apply ModuleCat.hom_ext
    apply (LinearMap.ringLmapEquivSelf (X.presheaf.stalk x) (X.presheaf.stalk x)
      ((schemeModuleStalkModuleFunctor X x).obj E)).injective
    change cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U ⟨x, hxU⟩ O E
        (u.hom ≫ schemeModuleSectionOnOpenHom E U (s j.as)) (a.inv 1) = m j.as
    exact (cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_section U ⟨x, hxU⟩ E
      (s j.as)).trans (hs j.as).1
  exact ⟨U, hxU, hU, v, hv, hvl⟩

end PfaffianDescent

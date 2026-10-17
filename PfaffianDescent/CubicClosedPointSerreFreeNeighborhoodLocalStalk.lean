import PfaffianDescent.SchemeModuleLocalIsoGerm
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodSectionNaturality

/-! # Native stalks of actual morphisms on a neighborhood -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual module morphism on an open induces a linear map of the
original ambient stalks, over the original ambient local ring. -/
def cubicClosedPointSerreFreeNeighborhoodLocalStalkMap
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M N : X.Modules)
    (p : M.restrict U.ι ⟶ N.restrict U.ι) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj M ⟶
      (schemeModuleStalkModuleFunctor X (U.ι x)).obj N := by
  letI := schemeModuleStalkModule M (U.ι x)
  letI := schemeModuleStalkModule N (U.ι x)
  letI := schemeModuleStalkModule (M.restrict U.ι) x
  letI := schemeModuleStalkModule (N.restrict U.ι) x
  let a := (Scheme.Modules.restrictStalkNatIso U.ι x).app M
  let b := (Scheme.Modules.restrictStalkNatIso U.ι x).app N
  let ai : M.presheaf.stalk (U.ι x) →+ (M.restrict U.ι).presheaf.stalk x := a.inv.hom
  let bh : (N.restrict U.ι).presheaf.stalk x →+ N.presheaf.stalk (U.ι x) := b.hom.hom
  let f := schemeModuleStalkLinearMap p x
  let l : M.presheaf.stalk (U.ι x) →ₗ[X.presheaf.stalk (U.ι x)]
      N.presheaf.stalk (U.ι x) :=
    { toFun := fun m => bh (f (ai m))
      map_add' := by intro m n; simp only [map_add]
      map_smul' := by
        intro r m
        have ha : ai (r • m) = U.ι.stalkMap x r • ai m :=
          schemeModuleRestrictStalk_inv_smul U x M r m
        rw [ha, f.map_smul]
        exact schemeModuleRestrictStalk_hom_smul U x N r _ }
  exact ModuleCat.ofHom l

/-- The ambient stalk map of an actually restricted global morphism is
its original native stalk map. -/
theorem cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_restrict
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M N : X.Modules) (p : M ⟶ N) :
    cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M N
      ((Scheme.Modules.restrictFunctor U.ι).map p) =
      (schemeModuleStalkModuleFunctor X (U.ι x)).map p := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have hn := congrArg (fun f => f.hom ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M m))
    ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.naturality p)
  simp only [ConcreteCategory.comp_apply] at hn
  have hk : (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
      ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M m) = m :=
    Iso.inv_hom_id_apply ((Scheme.Modules.restrictStalkNatIso U.ι x).app M) m
  rw [hk] at hn
  exact hn

/-- Native ambient stalk maps on a neighborhood preserve composition. -/
theorem cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_comp
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M N P : X.Modules)
    (p : M.restrict U.ι ⟶ N.restrict U.ι)
    (q : N.restrict U.ι ⟶ P.restrict U.ι) :
    cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M P (p ≫ q) =
      cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M N p ≫
        cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x N P q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app P
      (schemeModuleStalkLinearMap (p ≫ q) x
        ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M m)) =
    (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app P
      (schemeModuleStalkLinearMap q x
        ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app N
          ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.app N
            (schemeModuleStalkLinearMap p x
              ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M m)))))
  have hk : (Scheme.Modules.restrictStalkNatIso U.ι x).inv.app N
      ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.app N
        (schemeModuleStalkLinearMap p x
          ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M m))) =
      schemeModuleStalkLinearMap p x
        ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M m) :=
    Iso.hom_inv_id_apply ((Scheme.Modules.restrictStalkNatIso U.ι x).app N) _
  rw [hk]
  apply congrArg ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.app P)
  exact congrArg (fun f => f.hom
    ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M m))
    ((schemeModuleStalkFunctor (U : Scheme) x).map_comp p q)

/-- An actual local map commutes with taking ambient germs of its actual
local section map. -/
theorem cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_germ
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M N : X.Modules)
    (p : M.restrict U.ι ⟶ N.restrict U.ι) (s : Γ(M, U)) :
    cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M N p
      (M.presheaf.germ U (U.ι x) x.2 s) =
      N.presheaf.germ U (U.ι x) x.2
        ((schemeModuleRestrictTopSectionIso U N).hom
          (p.val.app (Opposite.op ⊤) ((schemeModuleRestrictTopSectionIso U M).inv s))) := by
  let sm := (schemeModuleRestrictTopSectionIso U M).inv s
  let sn := p.val.app (Opposite.op ⊤) sm
  have hm : (Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M
      (M.presheaf.germ U (U.ι x) x.2 s) =
      (M.restrict U.ι).presheaf.germ ⊤ x trivial sm := by
    rw [← schemeModuleRestrictTopSectionIso_germ U x M s]
    exact Iso.hom_inv_id_apply _ _
  have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (X := (U : Scheme).toTopCat) (C := AddCommGrpCat.{u})
    ⊤ x trivial ((Scheme.Modules.toPresheaf (U : Scheme)).map p) sm
  change (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app N
      (schemeModuleStalkLinearMap p x
        ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M
          (M.presheaf.germ U (U.ι x) x.2 s))) = _
  rw [hm]
  have ht : (schemeModuleRestrictTopSectionIso U N).inv
      ((schemeModuleRestrictTopSectionIso U N).hom sn) = sn :=
    Iso.hom_inv_id_apply _ _
  have hn := schemeModuleRestrictTopSectionIso_germ U x N
    ((schemeModuleRestrictTopSectionIso U N).hom sn)
  rw [ht] at hn
  exact (congrArg ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.app N) hg).trans hn

/-- The local map supplied by an actual section sends the original unit
stalk generator to that section's original ambient germ. -/
theorem cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_section
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M : X.Modules) (s : Γ(M, U)) :
    cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x
      (SheafOfModules.unit X.ringCatSheaf) M
      ((Scheme.Modules.restrictUnitIso U.ι).hom ≫ schemeModuleSectionOnOpenHom M U s)
      ((schemeModuleUnitStalkIso X (U.ι x)).inv 1) =
      M.presheaf.germ U (U.ι x) x.2 s := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hunit : (schemeModuleUnitStalkIso X (U.ι x)).inv 1 =
      O.presheaf.germ U (U.ι x) x.2 (1 : Γ(X, U)) := by
    change presheafOfModules_unitStalkLinearEquiv X.presheaf (U.ι x) 1 = _
    have h := presheafOfModules_unitStalkAddEquiv_germ X.presheaf (U.ι x) U x.2 (1 : Γ(X, U))
    rw [map_one] at h
    exact h
  rw [hunit, cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_germ]
  have ho : (Scheme.Modules.restrictUnitIso U.ι).hom.val.app (Opposite.op ⊤)
      ((schemeModuleRestrictTopSectionIso U O).inv (1 : Γ(X, U))) = (1 : Γ((U : Scheme), ⊤)) := by
    change (U.ι.appIso ⊤).hom
      (X.presheaf.map (eqToIso U.ι_image_top.symm).inv.op (1 : Γ(X, U))) = 1
    simp only [map_one]
  change M.presheaf.germ U (U.ι x) x.2
      ((schemeModuleRestrictTopSectionIso U M).hom
        ((schemeModuleSectionOnOpenHom M U s).val.app (Opposite.op ⊤)
          ((Scheme.Modules.restrictUnitIso U.ι).hom.val.app (Opposite.op ⊤)
            ((schemeModuleRestrictTopSectionIso U O).inv (1 : Γ(X, U)))))) = _
  rw [ho]
  exact congrArg (M.presheaf.germ U (U.ι x) x.2)
    (schemeModuleSectionOnOpenHom_value M U s)

end PfaffianDescent

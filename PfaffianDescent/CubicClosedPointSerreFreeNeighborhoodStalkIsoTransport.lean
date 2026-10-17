import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodLocalStalk

/-! # Transport of constructed stalk bases to an actual open chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual restriction stalk comparison transports an original-local-
ring module isomorphism to the actual local ring of the open scheme. -/
def cubicClosedPointSerreFreeNeighborhoodStalkIsoTransport
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M N : X.Modules)
    (l : (schemeModuleStalkModuleFunctor X (U.ι x)).obj M ≅
      (schemeModuleStalkModuleFunctor X (U.ι x)).obj N) :
    (schemeModuleStalkModuleFunctor (U : Scheme) x).obj (M.restrict U.ι) ≅
      (schemeModuleStalkModuleFunctor (U : Scheme) x).obj (N.restrict U.ι) := by
  letI := schemeModuleStalkModule M (U.ι x)
  letI := schemeModuleStalkModule N (U.ι x)
  letI := schemeModuleStalkModule (M.restrict U.ι) x
  letI := schemeModuleStalkModule (N.restrict U.ι) x
  let a : (M.restrict U.ι).presheaf.stalk x ≃+ M.presheaf.stalk (U.ι x) :=
    ((Scheme.Modules.restrictStalkNatIso U.ι x).app M).addCommGroupIsoToAddEquiv
  let b : (N.restrict U.ι).presheaf.stalk x ≃+ N.presheaf.stalk (U.ι x) :=
    ((Scheme.Modules.restrictStalkNatIso U.ι x).app N).addCommGroupIsoToAddEquiv
  let e : M.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      N.presheaf.stalk (U.ι x) := l.toLinearEquiv
  let k : (M.restrict U.ι).presheaf.stalk x ≃ₗ[(U : Scheme).presheaf.stalk x]
      (N.restrict U.ι).presheaf.stalk x :=
    { toAddEquiv := a.trans (e.toAddEquiv.trans b.symm)
      map_smul' := by
        intro r m
        obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap x)).surjective r
        change b.symm (e (a (U.ι.stalkMap x s • m))) =
          U.ι.stalkMap x s • b.symm (e (a m))
        have ha := schemeModuleRestrictStalk_hom_smul U x M s m
        change a (U.ι.stalkMap x s • m) = s • a m at ha
        rw [ha, e.map_smul]
        exact schemeModuleRestrictStalk_inv_smul U x N s (e (a m)) }
  exact k.toModuleIso

/-- Conjugating a constructed ambient stalk basis preserves its actual
projection square, including a quotient map defined only on the chart. -/
theorem cubicClosedPointSerreFreeNeighborhoodStalkIsoTransport_projection
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M E N : X.Modules)
    (l : (schemeModuleStalkModuleFunctor X (U.ι x)).obj M ≅
      (schemeModuleStalkModuleFunctor X (U.ι x)).obj E)
    (p : E ⟶ N) (q : M.restrict U.ι ⟶ N.restrict U.ι)
    (hl : l.hom ≫ (schemeModuleStalkModuleFunctor X (U.ι x)).map p =
      cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M N q) :
    (cubicClosedPointSerreFreeNeighborhoodStalkIsoTransport U x M E l).hom ≫
      (schemeModuleStalkModuleFunctor (U : Scheme) x).map
        ((Scheme.Modules.restrictFunctor U.ι).map p) =
      (schemeModuleStalkModuleFunctor (U : Scheme) x).map q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  let a := (Scheme.Modules.restrictStalkNatIso U.ι x).app M
  let b := (Scheme.Modules.restrictStalkNatIso U.ι x).app E
  let c := (Scheme.Modules.restrictStalkNatIso U.ι x).app N
  apply (ConcreteCategory.bijective_of_isIso c.hom).injective
  have hb : b.hom (b.inv (l.hom (a.hom m))) = l.hom (a.hom m) :=
    Iso.inv_hom_id_apply b _
  have h := congrArg (fun f => f.hom (a.hom m)) hl
  change (schemeModuleStalkLinearMap p (U.ι x)) (l.hom (a.hom m)) =
    c.hom (schemeModuleStalkLinearMap q x (a.inv (a.hom m))) at h
  rw [Iso.hom_inv_id_apply] at h
  change c.hom (schemeModuleStalkLinearMap
      ((Scheme.Modules.restrictFunctor U.ι).map p) x (b.inv (l.hom (a.hom m)))) =
    c.hom (schemeModuleStalkLinearMap q x m)
  have hn' := congrArg (fun f => f.hom (b.inv (l.hom (a.hom m))))
    ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.naturality p)
  simp only [ConcreteCategory.comp_apply] at hn'
  change c.hom (schemeModuleStalkLinearMap
      ((Scheme.Modules.restrictFunctor U.ι).map p) x (b.inv (l.hom (a.hom m)))) =
    schemeModuleStalkLinearMap p (U.ι x) (b.hom (b.inv (l.hom (a.hom m)))) at hn'
  rw [hb] at hn'
  exact hn'.trans h

end PfaffianDescent

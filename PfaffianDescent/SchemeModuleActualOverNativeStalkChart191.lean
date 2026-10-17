import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodLocalStalk

/-! Source-only191. Actual over-site charts carried to native ambient stalks.
The existing restriction, native local map and composition laws are reused. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native over/restriction comparison, retaining its actual natural Iso. -/
def actualOverRestrictedChartIso191 (U : X.Opens) {M N : X.Modules}
    (e : M.over U ≅ N.over U) : M.restrict U.ι ≅ N.restrict U.ι :=
  ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
    (Scheme.Modules.overFunctorEquiv U).app N

/-- A genuine commuting over-site square remains the SAME restriction square. -/
theorem actualOverRestrictedChartIso_square191
    (U : X.Opens) {M N M' N' : X.Modules}
    (eM : M.over U ≅ M'.over U) (eN : N.over U ≅ N'.over U)
    (f : M ⟶ N) (g : M' ⟶ N')
    (h : f.over U ≫ eN.hom = eM.hom ≫ g.over U) :
    (Scheme.Modules.restrictFunctor U.ι).map f ≫
        (actualOverRestrictedChartIso191 U eN).hom =
      (actualOverRestrictedChartIso191 U eM).hom ≫
        (Scheme.Modules.restrictFunctor U.ι).map g := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let E := (Scheme.Modules.overEquiv U).functor
  let n := Scheme.Modules.overFunctorEquiv U
  have hf := n.inv.naturality f
  change R.map f ≫ (n.app N).inv = (n.app M).inv ≫ E.map (f.over U) at hf
  have hg := n.hom.naturality g
  change E.map (g.over U) ≫ (n.app N').hom = (n.app M').hom ≫ R.map g at hg
  have he := congrArg E.map h
  rw [E.map_comp, E.map_comp] at he
  dsimp only [actualOverRestrictedChartIso191, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (R.map f) (n.app N).inv, hf]
  simp only [Category.assoc]
  rw [← Category.assoc (E.map (f.over U)) (E.map eN.hom), he]
  simp only [Category.assoc]
  rw [hg]

/-- A one-layer value cut identifying the existing local Iso with the
existing genuine ambient local-stalk map. -/
theorem actualLocalStalkModuleIso_hom191
    (U : X.Opens) (x : U) (M N : X.Modules)
    (e : M.restrict U.ι ≅ N.restrict U.ι) :
    (schemeModuleLocalStalkModuleIso U x M N e).hom =
      cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x M N e.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rfl

/-- Native local composition and restriction laws transfer the actual
restriction square, without rebuilding a stalk colimit. -/
theorem actualLocalStalkModuleIso_square191
    (U : X.Opens) (x : U) {M N M' N' : X.Modules}
    (eM : M.restrict U.ι ≅ M'.restrict U.ι)
    (eN : N.restrict U.ι ≅ N'.restrict U.ι)
    (f : M ⟶ N) (g : M' ⟶ N')
    (h : (Scheme.Modules.restrictFunctor U.ι).map f ≫ eN.hom =
      eM.hom ≫ (Scheme.Modules.restrictFunctor U.ι).map g) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).map f ≫
        (schemeModuleLocalStalkModuleIso U x N N' eN).hom =
      (schemeModuleLocalStalkModuleIso U x M M' eM).hom ≫
        (schemeModuleStalkModuleFunctor X (U.ι x)).map g := by
  rw [actualLocalStalkModuleIso_hom191 U x N N' eN,
    actualLocalStalkModuleIso_hom191 U x M M' eM,
    ← cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_restrict U x M N f,
    ← cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_restrict U x M' N' g,
    ← cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_comp U x M N N'
      ((Scheme.Modules.restrictFunctor U.ι).map f) eN.hom,
    ← cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_comp U x M M' N'
      eM.hom ((Scheme.Modules.restrictFunctor U.ι).map g), h]

/-- The actual over-site chart, as an Iso over the ORIGINAL ambient local ring. -/
def actualOverNativeStalkChartIso191
    (U : X.Opens) (x : U) {M N : X.Modules}
    (e : M.over U ≅ N.over U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj M ≅
      (schemeModuleStalkModuleFunctor X (U.ι x)).obj N :=
  schemeModuleLocalStalkModuleIso U x M N (actualOverRestrictedChartIso191 U e)

/-- The entire actual over-site square is preserved by the native stalk chart. -/
theorem actualOverNativeStalkChartIso_square191
    (U : X.Opens) (x : U) {M N M' N' : X.Modules}
    (eM : M.over U ≅ M'.over U) (eN : N.over U ≅ N'.over U)
    (f : M ⟶ N) (g : M' ⟶ N')
    (h : f.over U ≫ eN.hom = eM.hom ≫ g.over U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).map f ≫
        (actualOverNativeStalkChartIso191 U x eN).hom =
      (actualOverNativeStalkChartIso191 U x eM).hom ≫
        (schemeModuleStalkModuleFunctor X (U.ι x)).map g :=
  actualLocalStalkModuleIso_square191 U x
    (actualOverRestrictedChartIso191 U eM)
    (actualOverRestrictedChartIso191 U eN) f g
    (actualOverRestrictedChartIso_square191 U eM eN f g h)

/-- If the over-site coefficient is the actual restriction of a GLOBAL
map, the native chart has precisely that global map's literal stalk map. -/
theorem actualOverNativeStalkChartIso_hom_of_global191
    (U : X.Opens) (x : U) {M N : X.Modules}
    (e : M.over U ≅ N.over U) (f : M ⟶ N) (h : f.over U = e.hom) :
    (actualOverNativeStalkChartIso191 U x e).hom =
      (schemeModuleStalkModuleFunctor X (U.ι x)).map f := by
  let E := (Scheme.Modules.overEquiv U).functor
  let n := Scheme.Modules.overFunctorEquiv U
  have hn := n.hom.naturality f
  change E.map (f.over U) ≫ (n.app N).hom =
    (n.app M).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map f at hn
  have hr : (actualOverRestrictedChartIso191 U e).hom =
      (Scheme.Modules.restrictFunctor U.ι).map f := by
    dsimp only [actualOverRestrictedChartIso191, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom]
    rw [← h]
    change (n.app M).inv ≫ (E.map (f.over U) ≫ (n.app N).hom) =
      (Scheme.Modules.restrictFunctor U.ι).map f
    rw [hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  dsimp only [actualOverNativeStalkChartIso191]
  rw [actualLocalStalkModuleIso_hom191, hr,
    cubicClosedPointSerreFreeNeighborhoodLocalStalkMap_restrict]

end PfaffianDescent

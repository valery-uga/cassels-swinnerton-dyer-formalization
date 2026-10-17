import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodSectionNaturality
import PfaffianDescent.LocalExtResidueInjective

/-! # Shrinking an actual unit-module coefficient to an isomorphism -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual stalk map of a unit-module endomorphism, in the canonical
unit coordinate, is multiplication by its actual coefficient germ. -/
theorem cubicClosedPointSerreFreeNeighborhood_unit_stalk_coefficient
    {X : Scheme.{u}}
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x : X) (a : X.presheaf.stalk x) :
    (schemeModuleUnitStalkIso X x).hom
      ((schemeModuleStalkModuleFunctor X x).map c ((schemeModuleUnitStalkIso X x).inv a)) =
      X.presheaf.germ ⊤ x trivial (unitEndomorphismValue c) * a := by
  change schemeModuleStalkToRingLinearMap c x
    (presheafOfModules_unitStalkLinearEquiv X.presheaf x a) = _
  conv_lhs => rw [← unitEndomorphismOfRegularFunction_value c]
  exact schemeModuleStalkToRingLinearMap_unitEndomorphismOfRegularFunction
    (unitEndomorphismValue c) x a

/-- An invertible actual unit-module stalk map has a unit coefficient germ. -/
theorem cubicClosedPointSerreFreeNeighborhood_unit_germ_isUnit_of_stalk_isIso
    {X : Scheme.{u}}
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x : X) [IsIso ((schemeModuleStalkModuleFunctor X x).map c)] :
    IsUnit (X.presheaf.germ ⊤ x trivial (unitEndomorphismValue c)) := by
  let F := schemeModuleStalkModuleFunctor X x
  let e := schemeModuleUnitStalkIso X x
  obtain ⟨m, hm⟩ := (ConcreteCategory.bijective_of_isIso (F.map c)).surjective (e.inv 1)
  have h := cubicClosedPointSerreFreeNeighborhood_unit_stalk_coefficient c x (e.hom m)
  rw [e.hom_inv_id_apply, hm, e.inv_hom_id_apply] at h
  exact isUnit_iff_exists_inv.mpr ⟨e.hom m, h.symm⟩

/-- A unit coefficient germ makes the actual unit-module stalk map invertible. -/
theorem cubicClosedPointSerreFreeNeighborhood_unit_stalk_isIso_of_germ_isUnit
    {X : Scheme.{u}}
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x : X)
    (h : IsUnit (X.presheaf.germ ⊤ x trivial (unitEndomorphismValue c))) :
    IsIso ((schemeModuleStalkModuleFunctor X x).map c) := by
  let e := schemeModuleUnitStalkIso X x
  let s := (LinearEquiv.smulOfUnit h.unit : X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
    X.presheaf.stalk x).toModuleIso
  have hs : (schemeModuleStalkModuleFunctor X x).map c = (e ≪≫ s ≪≫ e.symm).hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply (ConcreteCategory.bijective_of_isIso e.hom).injective
    change e.hom (((schemeModuleStalkModuleFunctor X x).map c) m) =
      e.hom (e.inv (s.hom (e.hom m)))
    rw [e.inv_hom_id_apply]
    change e.hom (((schemeModuleStalkModuleFunctor X x).map c) m) =
      (h.unit : X.presheaf.stalk x) * e.hom m
    rw [h.unit_spec]
    have hc := cubicClosedPointSerreFreeNeighborhood_unit_stalk_coefficient c x (e.hom m)
    rw [e.hom_inv_id_apply] at hc
    exact hc
  rw [hs]
  infer_instance

/-- A single invertible actual unit stalk map spreads to an actual
isomorphism on an affine neighborhood. -/
theorem cubicClosedPointSerreFreeNeighborhood_unit_exists_affine_isIso
    {X : Scheme.{u}}
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x : X) [IsIso ((schemeModuleStalkModuleFunctor X x).map c)] :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map c) := by
  have hx : x ∈ X.basicOpen (unitEndomorphismValue c) :=
    (X.mem_basicOpen_top _ x).mpr
      (cubicClosedPointSerreFreeNeighborhood_unit_germ_isUnit_of_stalk_isIso c x)
  obtain ⟨U, hU, hxU, hUB⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨U, hxU, hU, ?_⟩
  apply schemeModuleMap_isIso_of_stalk
  intro y
  have hcy : IsIso ((schemeModuleStalkModuleFunctor X (U.ι y)).map c) :=
    cubicClosedPointSerreFreeNeighborhood_unit_stalk_isIso_of_germ_isUnit c (U.ι y)
      ((X.mem_basicOpen_top _ (U.ι y)).mp (hUB y.2))
  letI := hcy
  let G := Scheme.Modules.toPresheaf (U : Scheme) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  have ha : IsIso ((schemeModuleStalkFunctor X (U.ι y)).map c) :=
    Functor.map_isIso (forget₂ (ModuleCat (X.presheaf.stalk (U.ι y))) AddCommGrpCat)
      ((schemeModuleStalkModuleFunctor X (U.ι y)).map c)
  letI := ha
  have hb : IsIso (G.map ((Scheme.Modules.restrictFunctor U.ι).map c)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι y) c).mpr ha
  have hh : IsIso ((forget₂ (ModuleCat ((U : Scheme).presheaf.stalk y)) AddCommGrpCat).map
      ((schemeModuleStalkModuleFunctor (U : Scheme) y).map
        ((Scheme.Modules.restrictFunctor U.ι).map c))) := by
    change IsIso (G.map ((Scheme.Modules.restrictFunctor U.ι).map c))
    exact hb
  letI := hh
  exact isIso_of_reflects_iso _
    (forget₂ (ModuleCat ((U : Scheme).presheaf.stalk y)) AddCommGrpCat)

end PfaffianDescent

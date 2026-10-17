import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodSection

/-! # Actual section morphisms commute with restriction and module maps -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Restricting an actual module morphism and applying a local section
morphism is the section morphism of the actual image section. -/
theorem cubicClosedPointSerreFreeNeighborhood_section_naturality
    {X : Scheme.{u}} (M N : X.Modules) (p : M ⟶ N) (U : X.Opens)
    (t : M.presheaf.obj (Opposite.op U)) :
    schemeModuleSectionOnOpenHom M U t ≫ (Scheme.Modules.restrictFunctor U.ι).map p =
      schemeModuleSectionOnOpenHom N U (p.val.app (Opposite.op U) t) := by
  apply (N.restrict U.ι).unitHomEquiv.injective
  ext V
  apply (ConcreteCategory.bijective_of_isIso (N.restrictAppIso U.ι V.unop).hom).injective
  let hVU : U.ι ''ᵁ V.unop ≤ U := by
    simpa only [U.ι_image_top] using
      (Scheme.Hom.image_mono U.ι (show V.unop ≤ ⊤ from le_top))
  change p.val.app (Opposite.op (U.ι ''ᵁ V.unop))
      ((M.restrictAppIso U.ι V.unop).hom
        ((schemeModuleSectionOnOpenHom M U t).val.app V
          (1 : Γ((U : Scheme.{u}), V.unop)))) =
    (N.restrictAppIso U.ι V.unop).hom
      ((schemeModuleSectionOnOpenHom N U (p.val.app (Opposite.op U) t)).val.app V
        (1 : Γ((U : Scheme.{u}), V.unop)))
  rw [schemeModuleSectionOnOpenHom_restrict_value',
    schemeModuleSectionOnOpenHom_restrict_value']
  exact PresheafOfModules.naturality_apply p.val (homOfLE hVU).op t

/-- The actual morphism supplied by the unit section is the inverse of the
actual restricted-unit comparison. -/
theorem cubicClosedPointSerreFreeNeighborhood_section_unit_one
    {X : Scheme.{u}} (U : X.Opens) :
    schemeModuleSectionOnOpenHom (SheafOfModules.unit X.ringCatSheaf) U (1 : Γ(X, U)) =
      (Scheme.Modules.restrictUnitIso U.ι).inv := by
  apply (cancel_mono (Scheme.Modules.restrictUnitIso U.ι).hom).mp
  have h := cubicClosedPointSerreFreeNeighborhood_section_comp_projection
    (SheafOfModules.unit X.ringCatSheaf) (𝟙 _) U (1 : Γ(X, U)) rfl
  have hi : (Scheme.Modules.restrictFunctor U.ι).map
      (𝟙 (SheafOfModules.unit X.ringCatSheaf)) = 𝟙 _ :=
    (Scheme.Modules.restrictFunctor U.ι).map_id _
  rw [hi, Category.id_comp] at h
  simpa only [Iso.inv_hom_id] using h

/-- An actual unit-module morphism restricts to the local section morphism
of its value on the actual unit section. -/
theorem cubicClosedPointSerreFreeNeighborhood_section_of_unit_hom
    {X : Scheme.{u}} (N : X.Modules)
    (p : SheafOfModules.unit X.ringCatSheaf ⟶ N) (U : X.Opens) :
    schemeModuleSectionOnOpenHom N U (p.val.app (Opposite.op U) (1 : Γ(X, U))) =
      (Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map p := by
  rw [← cubicClosedPointSerreFreeNeighborhood_section_naturality,
    cubicClosedPointSerreFreeNeighborhood_section_unit_one]

end PfaffianDescent

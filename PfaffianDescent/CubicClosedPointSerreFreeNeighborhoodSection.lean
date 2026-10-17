import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodLift

/-! # Actual local splittings supplied by section lifts -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- A lifted unit section supplies a right inverse to the actual restricted
projection, under the actual restricted-unit isomorphism. -/
theorem cubicClosedPointSerreFreeNeighborhood_section_comp_projection
    {X : Scheme.{u}} (M : X.Modules)
    (p : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (t : M.presheaf.obj (Opposite.op U))
    (ht : p.val.app (Opposite.op U) t = (1 : Γ(X, U))) :
    schemeModuleSectionOnOpenHom M U t ≫
      (Scheme.Modules.restrictFunctor U.ι).map p ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom = 𝟙 _ := by
  apply (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf).unitHomEquiv.injective
  ext V
  let hVU : U.ι ''ᵁ V.unop ≤ U := by
    simpa only [U.ι_image_top] using
      (Scheme.Hom.image_mono U.ι (show V.unop ≤ ⊤ from le_top))
  change (U.ι.appIso V.unop).hom
    (p.val.app (Opposite.op (U.ι ''ᵁ V.unop))
      ((M.restrictAppIso U.ι V.unop).hom
        ((schemeModuleSectionOnOpenHom M U t).val.app V
          (1 : Γ((U : Scheme.{u}), V.unop))))) = 1
  rw [schemeModuleSectionOnOpenHom_restrict_value' M U t V.unop]
  have hn := PresheafOfModules.naturality_apply p.val (homOfLE hVU).op t
  change p.val.app (Opposite.op (U.ι ''ᵁ V.unop))
      (M.presheaf.map (homOfLE hVU).op t) =
    X.presheaf.map (homOfLE hVU).op (p.val.app (Opposite.op U) t) at hn
  rw [hn, ht]
  simp only [map_one]

/-- Actual projection to the unit splits on an affine neighborhood of each
point, with every restriction and unit comparison constructed. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_affine_section
    {X : Scheme.{u}} (M : X.Modules)
    (p : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Epi p] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      ∃ s : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ⟶ M.restrict U.ι,
        s ≫ (Scheme.Modules.restrictFunctor U.ι).map p ≫
          (Scheme.Modules.restrictUnitIso U.ι).hom = 𝟙 _ := by
  obtain ⟨U, hxU, hU, t, ht⟩ :=
    cubicClosedPointSerreFreeNeighborhood_exists_affine_unit_lift M p x
  exact ⟨U, hxU, hU, schemeModuleSectionOnOpenHom M U t,
    cubicClosedPointSerreFreeNeighborhood_section_comp_projection M p U t ht⟩

end PfaffianDescent

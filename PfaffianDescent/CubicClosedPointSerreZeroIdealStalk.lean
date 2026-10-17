import PfaffianDescent.VoisinSheafStalk
import PfaffianDescent.FieldPointExtCoordinate

/-! # Germs of the actual affine closed-immersion ideal -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The germ localization of the actual affine kernel ideal is the actual
range of its literal ideal-module stalk inclusion. This is proved by
lifting affine ideal sections and shrinking arbitrary stalk representatives
to affine opens. -/
theorem cubicClosedPointSerreZeroIdealStalk_range_eq_map
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    letI := schemeModuleStalkModule
      (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
    LinearMap.range (closedImmersionModuleStalkToRingLinearMap i x) =
      (i.ker.ideal U).map (X.presheaf.germ U.1 x hx).hom := by
  let M : X.Modules := IdealSheafDataModule.closedImmersionModule i
  letI := schemeModuleStalkModule M x
  change LinearMap.range
      (schemeModuleStalkToRingLinearMap (IdealSheafDataModule.closedImmersionModuleToUnit i) x) = _
  apply le_antisymm
  · intro y hy
    obtain ⟨m, rfl⟩ := hy
    obtain ⟨V₀, hV₀U, hxV₀, m₀, hm₀⟩ := M.presheaf.exists_le_germ_eq m hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVV₀⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV₀ V₀.2
    let VA : X.affineOpens := ⟨V, hV⟩
    let mV := M.presheaf.map (homOfLE hVV₀).op m₀
    have hmV : (TopCat.Presheaf.germ M.presheaf V x hxV) mV = m := by
      exact (M.presheaf.germ_res_apply (homOfLE hVV₀) x hxV m₀).trans hm₀
    rw [← hmV, schemeModuleStalkToRingLinearMap_germ]
    have hmem := IdealSheafDataModule.closedImmersionModule_section_mem_ker_ideal i VA mV
    rw [← i.ker.map_ideal (hVV₀.trans hV₀U)] at hmem
    have hmap := Ideal.mem_map_of_mem (X.presheaf.germ V x hxV).hom hmem
    simp only [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res'] at hmap
    exact hmap
  · change (i.ker.ideal U).map (X.presheaf.germ U.1 x hx).hom ≤
      (LinearMap.range
        (schemeModuleStalkToRingLinearMap (IdealSheafDataModule.closedImmersionModuleToUnit i) x) :
          Ideal (X.presheaf.stalk x))
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨m, hm⟩ := IdealSheafDataModule.exists_closedImmersionModule_section_of_affine_mem
      i U a ha
    refine ⟨TopCat.Presheaf.germ M.presheaf U.1 x hx m, ?_⟩
    rw [schemeModuleStalkToRingLinearMap_germ, hm]

/-- The actual affine ideal's germ localization is the kernel of the
literal point-support quotient map on the original stalk. -/
theorem cubicClosedPointSerreZeroIdealStalk_map_eq_ker
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    letI := schemeModuleStalkModule
      (show X.Modules from (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) x
    (i.ker.ideal U).map (X.presheaf.germ U.1 x hx).hom =
      LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap i x) := by
  letI := schemeModuleStalkModule
    (show X.Modules from IdealSheafDataModule.closedImmersionModule i) x
  letI := schemeModuleStalkModule
    (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) x
  exact (cubicClosedPointSerreZeroIdealStalk_range_eq_map i U x hx).symm.trans
    (closedImmersionModule_stalk_range_eq_ker_from_ring i x)

/-- At an original closed field point, the actual affine ideal localizes
to the original local ring's maximal ideal. -/
theorem cubicClosedPointSerreZeroIdealStalk_map_eq_maximal
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (x : Spec (.of L)) (hx : i x ∈ U.1) :
    (i.ker.ideal U).map (X.presheaf.germ U.1 (i x) hx).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)) := by
  letI := schemeModuleStalkModule
    (show X.Modules from (Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) (i x)
  exact (cubicClosedPointSerreZeroIdealStalk_map_eq_ker i U (i x) hx).trans
    (closedFieldPoint_pushforwardStalkFromRingLinearMap_ker_eq_maximalIdeal i x)

/-- Outside the actual closed support, the actual affine ideal's germ
localization is the unit ideal. -/
theorem cubicClosedPointSerreZeroIdealStalk_map_eq_top_off_range
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1) (hoff : x ∉ Set.range i) :
    (i.ker.ideal U).map (X.presheaf.germ U.1 x hx).hom = ⊤ := by
  let N : X.Modules := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  letI := schemeModuleStalkModule N x
  letI : Subsingleton (N.presheaf.stalk x) :=
    schemeModulePushforward_stalk_subsingleton_off_range i
      (SheafOfModules.unit Z.ringCatSheaf) x hoff
  rw [cubicClosedPointSerreZeroIdealStalk_map_eq_ker i U x hx]
  apply top_unique
  intro r _
  change closedImmersionPushforwardStalkFromRingLinearMap i x r = 0
  exact Subsingleton.elim _ _

/-- Away from the original closed field point, the literal original affine
ideal localizes to the unit ideal. -/
theorem cubicClosedPointSerreZeroIdealStalk_map_eq_top_off_point
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (x : X) (hx : x ∈ U.1) (hoff : x ≠ i default) :
    (i.ker.ideal U).map (X.presheaf.germ U.1 x hx).hom = ⊤ := by
  apply cubicClosedPointSerreZeroIdealStalk_map_eq_top_off_range i U x hx
  rintro ⟨z, rfl⟩
  exact hoff (congrArg i (Subsingleton.elim z default))

end PfaffianDescent

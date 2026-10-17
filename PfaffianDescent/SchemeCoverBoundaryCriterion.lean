import PfaffianDescent.SchemeCoverBoundaryInvariance

/-! # Detecting boundaries from intrinsic covering classes -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Only degree-one acyclicity of the degree-zero term is needed to detect
whether a covering cocycle is a boundary. -/
theorem schemeCoverDegreeTwoToCohomology_eq_iff_boundary_difference
    {X : Scheme.{u}} {ι : Type u} (W : ι → X.Opens)
    (hW : (Opens.grothendieckTopology X).CoversTop W)
    [hExt : HasExt.{u} X.Modules] (Y : X.Modules)
    [Subsingleton (Ext.{u} (C := X.Modules)
      ((sectionRepresenterCechChain X.ringCatSheaf W).X 0) Y 1)]
    (z z' : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf W).d 3 2) (Y := Y)) :
    schemeCoverDegreeTwoToCohomology W hW Y z =
      schemeCoverDegreeTwoToCohomology W hW Y z' ↔
    ∃ b : (sectionRepresenterCechChain X.ringCatSheaf W).X 1 ⟶ Y,
      (sectionRepresenterCechChain X.ringCatSheaf W).d 2 1 ≫ b = z.1 - z'.1 := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let C := sectionRepresenterCechChain X.ringCatSheaf W
  let P : X.Modules := (sectionRepresenterCechAugmented X.ringCatSheaf W ⊤ isTerminalTop).right
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf W ⊤ isTerminalTop
  let he := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf W hW ⊤ isTerminalTop
  letI : Epi eps := he.2
  let F : DegreeTwoCocycle (C.d 3 2) (Y := Y) →+ Ext.{u} (C := X.Modules) P Y 2 :=
    { toFun := schemeCoverDegreeTwoToExt W hW Y
      map_zero' := augmentedChainDegreeTwoToExt_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      map_add' := augmentedChainDegreeTwoToExt_add _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ }
  let e : Ext.{u} (C := X.Modules) P Y 2 ≃+ schemeModuleCohomology X Y 2 :=
    extPrecompIsoOfIso (schemeCoverCechTargetIsoUnit W)
  constructor
  · intro h
    have heq : F z = F z' := e.injective h
    have hz : F (z - z') = 0 := by rw [map_sub, heq, sub_self]
    exact (augmentedChainDegreeTwoToExt_eq_zero_iff
      P (C.X 0) (C.X 1) (C.X 2) (C.X 3) Y eps (C.d 1 0) (C.d 2 1) (C.d 3 2)
      (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf W ⊤ isTerminalTop)
      (C.d_comp_d 2 1 0) (C.d_comp_d 3 2 1)
      he.1 (schemeCoverCech_exact_one W hW) (schemeCoverCech_exact_two W hW)
      (z - z')).mp hz
  · rintro ⟨b, hb⟩
    exact schemeCoverDegreeTwoToCohomology_eq_of_boundary_difference W hW Y z z' b hb
end PfaffianDescent

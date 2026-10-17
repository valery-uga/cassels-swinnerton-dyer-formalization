import PfaffianDescent.SchemeCoverIntrinsicCohomology
import PfaffianDescent.CechExtBoundaryInvariance

/-!
# Boundaries preserve intrinsic covering cohomology

This comparison does not require an affine or acyclic covering family.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
theorem schemeCoverDegreeTwoToCohomology_eq_of_boundary_difference
    {X : Scheme.{u}} {ι : Type u} (W : ι → X.Opens)
    (hW : (Opens.grothendieckTopology X).CoversTop W)
    [hExt : HasExt.{u} X.Modules] (Y : X.Modules)
    (z z' : DegreeTwoCocycle ((sectionRepresenterCechChain X.ringCatSheaf W).d 3 2) (Y := Y))
    (b : (sectionRepresenterCechChain X.ringCatSheaf W).X 1 ⟶ Y)
    (hb : (sectionRepresenterCechChain X.ringCatSheaf W).d 2 1 ≫ b = z.1 - z'.1) :
    schemeCoverDegreeTwoToCohomology W hW Y z =
      schemeCoverDegreeTwoToCohomology W hW Y z' := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let C := sectionRepresenterCechChain X.ringCatSheaf W
  let P : X.Modules := (sectionRepresenterCechAugmented X.ringCatSheaf W ⊤ isTerminalTop).right
  let eps := sectionRepresenterCechAugmentation X.ringCatSheaf W ⊤ isTerminalTop
  let he := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    X.ringCatSheaf W hW ⊤ isTerminalTop
  letI : Epi eps := he.2
  have h : schemeCoverDegreeTwoToExt W hW Y z = schemeCoverDegreeTwoToExt W hW Y z' := by
    exact augmentedChainDegreeTwoToExt_eq_of_boundary_difference
      P (C.X 0) (C.X 1) (C.X 2) (C.X 3) Y eps (C.d 1 0) (C.d 2 1) (C.d 3 2)
      (sectionRepresenterCech_d_one_zero_comp_augmentation X.ringCatSheaf W ⊤ isTerminalTop)
      (C.d_comp_d 2 1 0) (C.d_comp_d 3 2 1)
      he.1 (schemeCoverCech_exact_one W hW) (schemeCoverCech_exact_two W hW) z z' b hb
  exact congrArg (fun t ↦
    (Ext.mk₀ (C := X.Modules) (schemeCoverCechTargetIsoUnit W).inv).comp t (zero_add 2)) h

end PfaffianDescent

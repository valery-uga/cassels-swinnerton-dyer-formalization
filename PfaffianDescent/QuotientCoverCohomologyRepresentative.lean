import PfaffianDescent.QuotientCoverIntrinsicComparison

/-! # Coordinate-cover representatives for every intrinsic negative-twist class -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {σ : Type} [Finite σ]
local notation "AA" => MvPolynomial.homogeneousSubmodule σ K

set_option backward.isDefEq.respectTransparency false in
/-- The actual projective coordinate cover supplies a representative for every
intrinsic degree-two negative-twist class, rather than assuming one exists. -/
theorem quotient_coordinateCover_intrinsic_surjective
    (I : HomogeneousIdeal AA) [hExt : HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) :
    letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
    Function.Surjective (schemeCoverDegreeTwoToCohomology
      (fun j : ULift.{u} σ => quotientCoordinateOpen I j.down)
      (quotientCoordinateOpenTop_coversTop I) (sheafOfModules (grading I) m)) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading I)).ringCatSheaf) := hExt
  let e : Ext.{u} (quotientSectionRepresenterCechTarget I)
      (sheafOfModules (grading I) m) 2 ≃+
      schemeModuleCohomology (Proj (grading I)) (sheafOfModules (grading I) m) 2 :=
    extPrecompIsoOfIso (quotientSectionRepresenterCechTargetIsoUnit I)
  have hs : Function.Surjective (fun w => e (quotientCechDegreeTwoToAugmentedExt I m w)) :=
    e.surjective.comp
      (@quotientCechDegreeTwoToAugmentedExt_surjective K σ inferInstance inferInstance I hExt m)
  exact hs

end PfaffianDescent.ProjectiveNegativeTwist

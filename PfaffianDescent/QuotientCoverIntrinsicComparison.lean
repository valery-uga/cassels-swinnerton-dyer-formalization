import PfaffianDescent.VoisinQuotientCechExtComparison
import PfaffianDescent.SchemeCoverIntrinsicCohomology

/-!
# Compatibility with the existing projective-quotient Cech calculation

The arbitrary-cover comparison specializes to the previously constructed
projective coordinate-cover comparison. No new comparison equality is
assumed when the refinement machinery is applied to that calculation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {σ : Type} [Finite σ]

local notation "AA" => MvPolynomial.homogeneousSubmodule σ K

theorem quotientSectionRepresenterCechTargetIsoUnit_eq_schemeCover
    (I : HomogeneousIdeal AA) :
    quotientSectionRepresenterCechTargetIsoUnit I =
      schemeCoverCechTargetIsoUnit (fun j : ULift.{u} σ => quotientCoordinateOpen I j.down) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem quotientCechDegreeTwoToAugmentedExt_eq_schemeCover
    (I : HomogeneousIdeal AA) [HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) (z : QuotientCechDegreeTwoCocycle I m) :
    quotientCechDegreeTwoToAugmentedExt I m z =
      schemeCoverDegreeTwoToExt (fun j : ULift.{u} σ => quotientCoordinateOpen I j.down)
        (quotientCoordinateOpenTop_coversTop I) (sheafOfModules (grading I) m) z := rfl

set_option backward.isDefEq.respectTransparency false in
theorem schemeCoverDegreeTwoToCohomology_quotient_coordinateCover
    (I : HomogeneousIdeal AA) [hExt : HasExt.{u} (Proj (grading I)).Modules]
    (m : ℕ) (z : QuotientCechDegreeTwoCocycle I m) :
    schemeCoverDegreeTwoToCohomology
        (fun j : ULift.{u} σ => quotientCoordinateOpen I j.down)
        (quotientCoordinateOpenTop_coversTop I) (sheafOfModules (grading I) m) z =
      (Ext.mk₀ (C := (Proj (grading I)).Modules)
        (quotientSectionRepresenterCechTargetIsoUnit I).inv).comp
        (quotientCechDegreeTwoToAugmentedExt I m z) (zero_add 2) := rfl

end PfaffianDescent.ProjectiveNegativeTwist

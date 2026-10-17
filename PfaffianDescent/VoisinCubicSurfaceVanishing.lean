import PfaffianDescent.VoisinGlobalExtVanishing
import PfaffianDescent.VoisinHypersurfaceTwist
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-! # The cubic-surface cohomology vanishings used in Voisin's construction

The ambient P³ cohomology assumptions in the restriction-sequence lemmas
are discharged here by the checked standard-cover computation.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The structure sheaf of P³ has vanishing first cohomology. -/
theorem p3_structure_cohomology_one_subsingleton
    [HasExt.{u} (Proj PS).Modules] :
    Subsingleton (schemeModuleCohomology (Proj PS)
      (SheafOfModules.unit (Proj PS).ringCatSheaf) 1) := by
  letI := (p3_negativeTwist_cohomology_one_and_two_subsingleton K 0).1
  exact ext_subsingleton_of_iso_right (C := (Proj PS).Modules)
    (X := SheafOfModules.unit (Proj PS).ringCatSheaf)
    (unitIsoZeroTwist PS).symm 1

/-- The homogeneous coordinate ring of a nonzero smooth cubic is a domain.
This turns smoothness into the algebraic primality input used by the concrete
twist and cohomology computations. -/
theorem smoothCubic_coordinateRing_isDomain
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    IsDomain (CoordinateRing (equationIdeal p hp)) := by
  change IsDomain (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set _))
  exact (Ideal.Quotient.isDomain_iff_prime _).mpr
    (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)

set_option backward.isDefEq.respectTransparency false in
/-- Voisin's negative-three vanishing on a cubic surface, with no ambient
cohomology vanishing assumed. -/
theorem cubicSurface_negativeThree_cohomology_one
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    Subsingleton (schemeModuleCohomology (hypersurface p hp)
      (sheafOfModules (grading (equationIdeal p hp)) 3) 1) := by
  letI : EnoughInjectives (hypersurface p hp).Modules :=
    sheafOfModules_enoughInjectives (hypersurface p hp).ringCatSheaf
  letI := (p3_negativeTwist_cohomology_one_and_two_subsingleton K 3).1
  letI := (p3_negativeTwist_cohomology_one_and_two_subsingleton K 6).2
  exact cubicHypersurface_negativeThree_cohomology_one_subsingleton p hp hp0

set_option backward.isDefEq.respectTransparency false in
/-- The structure-sheaf vanishing on a cubic surface, with no ambient
cohomology vanishing assumed. -/
theorem cubicSurface_structure_cohomology_one
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    Subsingleton (schemeModuleCohomology (hypersurface p hp)
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 1) := by
  letI : EnoughInjectives (hypersurface p hp).Modules :=
    sheafOfModules_enoughInjectives (hypersurface p hp).ringCatSheaf
  letI := p3_structure_cohomology_one_subsingleton K
  letI := (p3_negativeTwist_cohomology_one_and_two_subsingleton K 3).2
  exact cubicHypersurface_structure_cohomology_one_subsingleton p hp hp0

/-- Voisin's negative-three vanishing on a smooth cubic, with its coordinate
ring domain condition derived internally from smoothness. -/
theorem cubicSurface_negativeThree_cohomology_one_of_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    Subsingleton (schemeModuleCohomology (hypersurface p hp)
      (sheafOfModules (grading (equationIdeal p hp)) 3) 1) := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) :=
    smoothCubic_coordinateRing_isDomain K p hp hp0
  exact cubicSurface_negativeThree_cohomology_one K p hp hp0

/-- The structure-sheaf degree-one vanishing on a smooth cubic, with the
coordinate-ring domain condition derived internally from smoothness. -/
theorem cubicSurface_structure_cohomology_one_of_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    Subsingleton (schemeModuleCohomology (hypersurface p hp)
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 1) := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) :=
    smoothCubic_coordinateRing_isDomain K p hp hp0
  exact cubicSurface_structure_cohomology_one K p hp hp0

end PfaffianDescent.ProjectiveNegativeTwist

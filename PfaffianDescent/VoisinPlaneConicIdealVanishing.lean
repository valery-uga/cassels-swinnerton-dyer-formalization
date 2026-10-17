import PfaffianDescent.VoisinPlaneConicNonempty
import PfaffianDescent.VoisinCubicConstantFunctions

/-!
# Vanishing for the actual plane-conic ideal on a smooth cubic

The concrete plane–quadric intersection is a nonempty closed subscheme.
The smooth cubic's global functions are constant, so the ideal sheaf of
this actual immersion has no nonzero global section. This conclusion does
not require its Cartier presentation.
-/

namespace PfaffianDescent.ProjectiveNegativeTwist

open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The global ideal sections of the actual plane–quadric intersection
inside a smooth cubic vanish. -/
theorem p3_smoothCubicPlaneConicIdeal_sections_subsingleton
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hell : ell.IsHomogeneous 1)
    (hq : q.IsHomogeneous 2) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))) :
    Subsingleton
      (IdealSheafDataModule.closedImmersionModule
        (planeConicToCubic p ell q hp hell hq hpc)).sections := by
  letI : IsClosedImmersion (planeConicToCubic p ell q hp hell hq hpc) :=
    planeConicToCubic_isClosedImmersion p ell q hp hell hq hpc
  letI : Nonempty (planeConicScheme ell q hell hq) :=
    planeConicScheme_nonempty ell q hell hq
  exact p3_smoothCubicNonemptyIdeal_sections_subsingleton K p hp hp0
    (planeConicToCubic p ell q hp hell hq hpc)

end PfaffianDescent.ProjectiveNegativeTwist

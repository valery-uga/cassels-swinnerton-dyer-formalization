import PfaffianDescent.VoisinPlaneConicIdealVanishing
import PfaffianDescent.VoisinCartierInverseTwist

/-!
# No sections of the inverse twist of an actual plane conic

For a plane conic lying on a smooth cubic, the already checked ideal-sheaf
vanishing is precisely the vanishing needed by the twisted Serre sequence
once the actual immersion is certified to be an effective Cartier divisor.
-/

namespace PfaffianDescent.ProjectiveNegativeTwist

open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

theorem p3_smoothCubicPlaneConic_inverseCartierTwist_sections_subsingleton
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hell : ell.IsHomogeneous 1)
    (hq : q.IsHomogeneous 2) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K)))
    [IsClosedImmersion (planeConicToCubic p ell q hp hell hq hpc)]
    (H : RegularPrincipalImmersion (planeConicToCubic p ell q hp hell hq hpc)) :
    Subsingleton H.inverseCartierTwist.sections := by
  change Subsingleton
    (IdealSheafDataModule.closedImmersionModule
      (planeConicToCubic p ell q hp hell hq hpc)).sections
  exact p3_smoothCubicPlaneConicIdeal_sections_subsingleton
    K p ell q hp hell hq hp0 hpc

end PfaffianDescent.ProjectiveNegativeTwist

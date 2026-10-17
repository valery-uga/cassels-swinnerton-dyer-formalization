import PfaffianDescent.VoisinPlaneConicInverseTwistH0
import PfaffianDescent.VoisinSerreCartierTwistInjection

/-!
# The twisted Serre injection for an actual plane conic

On a smooth cubic, an actual nonempty plane conic has no inverse-twist
sections. If its closed immersion has a regular-principal certificate, its
Cartier charts also make tensoring a Serre sequence exact. Together these
give the literal section injection used in the conic branch.
-/

namespace PfaffianDescent.ProjectiveNegativeTwist

open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

theorem p3_smoothCubicPlaneConic_twistedSerreProjection_sections_injective
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hell : ell.IsHomogeneous 1)
    (hq : q.IsHomogeneous 2) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K)))
    [IsClosedImmersion (planeConicToCubic p ell q hp hell hq hpc)]
    (H : RegularPrincipalImmersion (planeConicToCubic p ell q hp hell hq hpc))
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    (e : SerreExtensionSequenceData (hypersurface p hp) M) :
    Function.Injective (SheafOfModules.sectionsMap
      (e.twistedComplex H.inverseCartierTwist).g) := by
  letI : Subsingleton H.inverseCartierTwist.sections :=
    p3_smoothCubicPlaneConic_inverseCartierTwist_sections_subsingleton
      K p ell q hp hell hq hp0 hpc H
  exact e.twistedProjection_sections_injective_of_cartier H

end PfaffianDescent.ProjectiveNegativeTwist

import PfaffianDescent.VoisinCoordinateOnePDeriv
import PfaffianDescent.VoisinPlaneConicSerreJacobianEndpoint

/-!
# The plane-conic Serre input from smoothness alone

The reverse Jacobian criterion on each actual smooth-cubic chart supplies
the only remaining premise of the projective Cartier gluing argument. This
constructs a regular-principal immersion of the actual plane conic and the
twisted Serre global-section injection without a separate Jacobian or
Cartier hypothesis.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def planeConicToCubic_regularPrincipalImmersion_of_smoothCubic
    (p ell q a b : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2)
    (h : p = ell * a + q * b) :
    RegularPrincipalImmersion
      (planeConicToCubic p ell q hp hell hq
        (cubic_mem_planeConicIdeal_of_decomposition p ell q a b h)) :=
  planeConicToCubic_regularPrincipalImmersion_of_chartJacobian_top
    p ell q a b hp hp0 hell hell0 hq h
    (smoothCubic_chartJacobian_top p hp hp0)

end PfaffianDescent

namespace PfaffianDescent.ProjectiveNegativeTwist

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- For an actual plane conic on a nonzero smooth cubic, the twisted Serre
projection is injective on literal global sections. -/
theorem p3_smoothCubicPlaneConic_twistedSerreProjection_sections_injective_of_smooth
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p ell q a b : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2)
    (h : p = ell * a + q * b)
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    (e : SerreExtensionSequenceData (hypersurface p hp) M) :
    let H := PfaffianDescent.planeConicToCubic_regularPrincipalImmersion_of_smoothCubic
      p ell q a b hp hp0 hell hell0 hq h
    Function.Injective (SheafOfModules.sectionsMap
      (e.twistedComplex H.inverseCartierTwist).g) := by
  exact p3_smoothCubicPlaneConic_twistedSerreProjection_sections_injective_of_chartJacobian_top
    K p ell q a b hp hp0 hell hell0 hq h
    (PfaffianDescent.smoothCubic_chartJacobian_top p hp hp0) e

end PfaffianDescent.ProjectiveNegativeTwist

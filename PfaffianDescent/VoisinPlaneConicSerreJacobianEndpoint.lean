import PfaffianDescent.VoisinPlaneConicPrincipalOpenImmersion
import PfaffianDescent.VoisinPlaneConicSerreInjection

/-!
# Twisted Serre section injection for the actual plane conic

The chartwise Jacobian unit-ideal condition gives explicit principal-open
Cartier charts for the conic and hence the literal global-section injection
in the twisted Serre sequence. No abstract Cartier certificate is assumed.
-/

namespace PfaffianDescent.ProjectiveNegativeTwist

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] PfaffianDescent.planeConicToCubic_isClosedImmersion
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

theorem p3_smoothCubicPlaneConic_twistedSerreProjection_sections_injective_of_chartJacobian_top
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p ell q a b : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2)
    (h : p = ell * a + q * b)
    (hjac : ∀ j : Fin 4,
      let I := equationIdeal p hp
      Ideal.span (Set.range (fun i : Fin 4 =>
        (pderiv i p).eval₂ (chartBaseMap I j) (chartCoordinate I j))) = ⊤)
    {M : SheafOfModules.{u} (hypersurface p hp).ringCatSheaf}
    (e : SerreExtensionSequenceData (hypersurface p hp) M) :
    let H := PfaffianDescent.planeConicToCubic_regularPrincipalImmersion_of_chartJacobian_top
      p ell q a b hp hp0 hell hell0 hq h hjac
    Function.Injective (SheafOfModules.sectionsMap
      (e.twistedComplex H.inverseCartierTwist).g) := by
  dsimp only
  let hpc := PfaffianDescent.cubic_mem_planeConicIdeal_of_decomposition
    p ell q a b h
  let H := PfaffianDescent.planeConicToCubic_regularPrincipalImmersion_of_chartJacobian_top
    p ell q a b hp hp0 hell hell0 hq h hjac
  exact p3_smoothCubicPlaneConic_twistedSerreProjection_sections_injective
    K p ell q hp hell hq hp0 hpc H e

end PfaffianDescent.ProjectiveNegativeTwist

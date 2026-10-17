import PfaffianDescent.CorayOriginalPlanePositiveEulerHOne
import PfaffianDescent.ActualPositiveEulerSectionEquationTransport230

/-! SOURCE ONLY / UNVERIFIED. The genuine frozen original point/diagonal
geometry produces the boundary internally. This module consumes that producer,
not a boundary, trace, conormal, positive-degree vanishing or genus certificate.
All endpoints are characteristic zero and keep the SAME original plane curve,
coefficient, field action, ENTIRE cut and literal native ideal-twist sequence.
The actual positive-boundary producer remains a separately checked prerequisite;
this source draft asserts no acceptance status for imported geometry. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MvPolynomial Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equation equality carries the whole coefficient/base-action property
from the literal generic cubic to the SAME actual rectangular plane cubic. -/
theorem charZero_actualRectangularPlane_positiveEulerSection_hOne_subsingleton001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let F := GenericHyperplaneField K
    let pE := PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
    let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
    let X := scheme (equationIdeal pE hpE)
    let pi := hypersurfaceToBase pE hpE
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear F X.Modules := schemeModulesLinearOver pi
    ∀ (M : X.Modules), schemeModuleLocallyRankOne M →
      ∀ (s : M.val.obj (op ⊤)), s ≠ 0 →
        0 < (Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
          Module.finrank F (schemeModuleCohomology X M 1) →
        Subsingleton (schemeModuleCohomology X M 1) := by
  let F := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
  have hEquation : genericPlaneCubic p = pE :=
    (genericPlaneInclusionMatrix_restrictedEquation p).symm
  exact planeCubicEquation_positiveEulerSectionProperty_transport230 (K := F)
    (genericPlaneCubic p) pE (genericPlaneCubic_isHomogeneous p hp) hpE hEquation
    (charZero_originalGenericPlane_positiveEulerSection_hOne_subsingleton001 p hp hp0)

/-- Positive actual Euler produces the section itself. No section, boundary
or positive-degree vanishing certificate is supplied by the geometric caller. -/
theorem charZero_actualRectangularPlane_positiveEuler_hOne_subsingleton001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let F := GenericHyperplaneField K
    let pE := PfaffianDescent.rectangularSubstitution
      (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
    let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
      (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
    let X := scheme (equationIdeal pE hpE)
    let pi := hypersurfaceToBase pE hpE
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear F X.Modules := schemeModulesLinearOver pi
    ∀ (M : X.Modules), schemeModuleLocallyRankOne M →
      0 < (Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
        Module.finrank F (schemeModuleCohomology X M 1) →
      Subsingleton (schemeModuleCohomology X M 1) := by
  classical
  dsimp only
  let F := GenericHyperplaneField K
  let pE := PfaffianDescent.rectangularSubstitution
    (genericPlaneInclusionMatrix (K := K)) (p.map (algebraMap K F))
  let hpE := PfaffianDescent.rectangularSubstitution_homogeneous
    (genericPlaneInclusionMatrix (K := K)) (hp.map (algebraMap K F))
  let X := scheme (equationIdeal pE hpE)
  let pi := hypersurfaceToBase pE hpE
  letI hNativeExt : HasExt.{u} X.Modules := schemeModules_hasExt X
  letI : Linear F X.Modules := schemeModulesLinearOver pi
  intro M hM hEuler
  obtain ⟨s, hs⟩ := @schemeModule_exists_nonzero_top_section_of_positiveEuler230.{u}
    F inferInstance X hNativeExt pi M hEuler
  exact charZero_actualRectangularPlane_positiveEulerSection_hOne_subsingleton001
    p hp hp0 M hM s hs hEuler


end PfaffianDescent.Coray

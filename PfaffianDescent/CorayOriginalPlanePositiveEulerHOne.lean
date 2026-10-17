import PfaffianDescent.CorayPlanePositiveEulerHOneNative
import PfaffianDescent.OriginalGenericPlanePositiveEulerBoundary227
import PfaffianDescent.OriginalGenericPlaneCubicHOneRank226

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

/-- Inferred complete actual original boundary FAMILY, with no concrete
M/section argument or expected result from the final H1 public header. -/
private def positiveEulerSection_originalBoundaryFamilyRawCut001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)] :=
  @originalGenericPlane_positiveEulerSection_boundaryNonzero227.{u}
    K inferInstance inferInstance p hp hp0 hSmooth

/-- Inferred actual original unit-H1 pair with its original structural action.
No target-group class is reconstructed in the final wrapper. -/
private def positiveEulerSection_originalUnitPairRawCut001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)] :=
  @smoothCubic_genericPlaneCubic_unit_cohomology_one_finite_finrank_eq_one226.{u}
    K inferInstance p hp hp0 hSmooth

/-- Complete actual whole-function application with its result inferred from
the EXACT native typed consumer. This isolates actual dictionaries/type matching
from the final conversion to the literal original public H1 header. -/
private def positiveEulerSection_originalWholePropertyRawCut001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)] :=
  @positiveEulerSection_nativePlaneWholePropertyCut001.{u}
    (GenericHyperplaneField K) inferInstance
    (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    (genericPlaneCubic_ne_zero p hp hp0)
    (smoothCubic_actualGenericPlaneCubic_smooth p hp hp0)
    (smoothCubic_actualGenericPlaneCubic_isIntegral p hp hp0)
    (@positiveEulerSection_originalBoundaryFamilyRawCut001.{u}
      K inferInstance inferInstance p hp hp0 hSmooth)
    (@positiveEulerSection_originalUnitPairRawCut001.{u}
      K inferInstance p hp hp0 hSmooth)

/-- The original point geometry produces nonzero of the SAME whole section
boundary. Rank-one unit H1 and whole quotient H1=0 then give actual H1(M)=0.
A positive Euler number and a genuine section are the only coefficient inputs. -/
theorem charZero_originalGenericPlane_positiveEulerSection_hOne_subsingleton001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let F := GenericHyperplaneField K
    let pE := genericPlaneCubic p
    let hpE := genericPlaneCubic_isHomogeneous p hp
    let X := hypersurface pE hpE
    let pi := hypersurfaceToBase pE hpE
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    letI : Linear F X.Modules := schemeModulesLinearOver pi
    ∀ (M : X.Modules), schemeModuleLocallyRankOne M →
      ∀ (s : M.val.obj (op ⊤)), s ≠ 0 →
        0 < (Module.finrank F (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
          Module.finrank F (schemeModuleCohomology X M 1) →
        Subsingleton (schemeModuleCohomology X M 1) := by
  exact @positiveEulerSection_originalWholePropertyRawCut001.{u}
    K inferInstance inferInstance p hp hp0 inferInstance


end PfaffianDescent.Coray

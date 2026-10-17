import PfaffianDescent.CorayWholePlaneIdealNativeHZeroInjection
import PfaffianDescent.CorayWholeSurfaceToPlaneCutCoordinateIdealRestriction
import PfaffianDescent.CorayActualGenericPlaneCubicIntegral

/-! ORIGINAL smooth cubic inputs derive the genuine native H0 injection
for the ENTIRE canonical Fin3 plane-cut ideal. This is not yet the ambient
transport to the rectangular E/Fin4 whole-cut coefficient of229/230.
SOURCE ONLY. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual original homogeneous plane-cut elements define native whole
ideal-twist sections. Its augmentation is the original homogeneous section. -/
def originalWholePlaneIdealGradeNativeHZeroMap
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hpC : p ∈ C.toIdeal) (d : ℕ) :
    let I := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    wholeIdealGrade (grading I) (wholeOriginalPlaneCutCoordinateIdeal C p hp) d →ₗ[GenericHyperplaneField K]
      SchemeModuleOpenSectionsOver (toBase I)
        (closedImmersionIdealTwist (wholeGenericCutPlaneIdealImmersion C p hp hpC)
          (positiveSheafOfModules (grading I) d)) ⊤ := by
  dsimp only
  exact wholePlaneIdealGradeNativeTopSectionLinearMap
    (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))
    (wholeGenericCutPlaneIdeal C)
    (genericPlaneCubic_ideal_le_wholeGenericCutPlaneIdeal C p hp hpC) d

/-- ORIGINAL smoothness and nonzero equation derive both domain and
projective nonemptiness, so no injectivity/integrality certificate is input. -/
theorem originalWholePlaneIdealGradeNativeHZeroMap_injective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hpC : p ∈ C.toIdeal) (d : ℕ) :
    Function.Injective (originalWholePlaneIdealGradeNativeHZeroMap p hp C hpC d) := by
  let I := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  letI : IsDomain (CoordinateRing I) := by
    change IsDomain (MvPolynomial (Fin 3) (GenericHyperplaneField K) ⧸
      Ideal.span ({genericPlaneCubic p} : Set _))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr
      (smoothCubic_actualGenericPlaneCubic_principalIdeal_prime p hp hp0)
  letI : Nonempty (scheme I) := smoothCubic_actualGenericPlaneCubic_nonempty p hp hp0
  exact wholePlaneIdealGradeNativeTopSectionLinearMap_injective I (wholeGenericCutPlaneIdeal C)
    (genericPlaneCubic_ideal_le_wholeGenericCutPlaneIdeal C p hp hpC) d

/-- The native ideal-twist H0 rank bounds the literal quotient-ideal grade.
Only finite dimensionality of that same H0, not a dimension value, is needed. -/
theorem originalWholePlaneIdealGrade_finrank_le_nativeHZero
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hpC : p ∈ C.toIdeal) (d : ℕ)
    [Module.Finite (GenericHyperplaneField K)
      (SchemeModuleOpenSectionsOver
        (toBase (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)))
        (closedImmersionIdealTwist (wholeGenericCutPlaneIdealImmersion C p hp hpC)
          (positiveSheafOfModules
            (grading (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))) d)) ⊤)] :
    Module.finrank (GenericHyperplaneField K)
      (wholeIdealGrade
        (grading (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)))
        (wholeOriginalPlaneCutCoordinateIdeal C p hp) d) ≤
    Module.finrank (GenericHyperplaneField K)
      (SchemeModuleOpenSectionsOver
        (toBase (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)))
        (closedImmersionIdealTwist (wholeGenericCutPlaneIdealImmersion C p hp hpC)
          (positiveSheafOfModules
            (grading (equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))) d)) ⊤) :=
  LinearMap.finrank_le_finrank_of_injective
    (originalWholePlaneIdealGradeNativeHZeroMap_injective p hp hp0 C hpC d)

end PfaffianDescent.Coray
end

import PfaffianDescent.CorayOwnCoordinateNativeCokernelRankAnyField
import PfaffianDescent.CorayOwnPositiveNativeEulerOriginalInputs

/-! SOURCE ONLY. Replace the original actual coordinate cokernel rank in
the proved native Euler step by its genuinely computed OWN Hilbert degree.
Degree-zero constants are retained unchanged; no genus certificate. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME original positive-coordinate native Euler difference is the
OWN Hilbert degree. Every finite-rank and quotient-rank input is derived
from original p/q/minimal-component geometry over the original field. -/
theorem selectedProjectiveMinimalComponent_ownPositiveCoordinate_nativeEuler_step_degree_anyField
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) (j : Fin 4) (hj : coordinate C j ∉ P.asHomogeneousIdeal)
    [HasExt.{u} (scheme C).Modules] (m : ℕ) :
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    ((Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
      (positiveSheafOfModules (grading C) (m + 1)) ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology (scheme C)
          (positiveSheafOfModules (grading C) (m + 1)) 1) =
      (Module.finrank K (SchemeModuleOpenSectionsOver (toBase C)
        (positiveSheafOfModules (grading C) m) ⊤) : ℤ) -
        Module.finrank K (schemeModuleCohomology (scheme C)
          (positiveSheafOfModules (grading C) m) 1) +
          actualCurveCoordinateHilbertDegree C) := by
  letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
  have hEuler := selectedProjectivePrimeComponent_ownPositiveCoordinate_nativeEuler_step_original
    p q hp hp0 n hq hnot C hCmin.le hCmin.isPrime P j hj m
  have hRank := (selectedProjectiveMinimalComponent_ownCoordinateCokernel_topSections_finite_and_hilbertDegree_anyField
    p q hp hp0 n hq hnot C hCmin P j hj m).2
  dsimp only at hEuler
  rw [hRank] at hEuler
  exact hEuler

end PfaffianDescent.Coray
end

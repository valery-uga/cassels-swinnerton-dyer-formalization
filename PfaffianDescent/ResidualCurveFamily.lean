import PfaffianDescent.CurveFamilyCycleQuotient
import PfaffianDescent.EffectiveSignedPushforward

/-!
# Residual cycles from actual curve families

The geometric residual constructions in Voisin's argument produce finite flat
families over a projective line.  This file turns the two decomposed endpoint
fibers of such a family into the precise effectivity statement in the cycle
quotient.
-/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory AllCharacteristics
universe u

section
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {p : X ⟶ Spec (.of K)} [IsSeparated p]

/-- If one endpoint of a finite-flat family is `z + r` and the other is
`n · h`, then the residual cycle `r` effectively represents `n[h] - [z]`.
This is the cycle-theoretic output used by both applications of Voisin's
Lemma 3.6. -/
theorem residualClass_effective_of_rationalCycleFamily
    (F : RationalCycleFamily p) (z r h : EffectiveZeroCycle X) (n : ℕ)
    (hzero : F.fiberCycle false = z + r)
    (hinfinity : F.fiberCycle true = n • h) :
    CurveFamilyCycleQuotient.IsEffective p
      (n • curveFamilyCycleClass p h.toZeroCycle -
        curveFamilyCycleClass p z.toZeroCycle) := by
  refine ⟨r, ?_⟩
  have hc := curveFamilyCycleClass_fibers p F
  rw [hzero, hinfinity, effectiveCycleToSigned_add,
    effectiveCycleToSigned_nsmul, map_add, map_nsmul] at hc
  apply (eq_sub_iff_add_eq).2
  simpa only [add_comm] using hc

/-- The same endpoint calculation with a single reference cycle gives the
rank-two-bundle subtraction `z - h`. -/
theorem subtractionClass_effective_of_rationalCycleFamily
    (F : RationalCycleFamily p) (z r h : EffectiveZeroCycle X)
    (hzero : F.fiberCycle false = h + r)
    (hinfinity : F.fiberCycle true = z) :
    CurveFamilyCycleQuotient.IsEffective p
      (curveFamilyCycleClass p z.toZeroCycle -
        curveFamilyCycleClass p h.toZeroCycle) := by
  refine ⟨r, ?_⟩
  have hc := curveFamilyCycleClass_fibers p F
  rw [hzero, hinfinity, effectiveCycleToSigned_add, map_add] at hc
  apply (eq_sub_iff_add_eq).2
  simpa only [add_comm] using hc

end
end PfaffianDescent

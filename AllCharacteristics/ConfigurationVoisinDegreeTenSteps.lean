import PfaffianDescent.VoisinCycleArithmetic
import AllCharacteristics.ConfigurationRationalCycleFamily
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PfaffianDescent
namespace AllCharacteristics.HomogeneousProjective
universe u v
variable {A : Type u} [CommRing A]
variable {K : Type u} [Field K]
variable {sigma : Type v} [SetLike sigma A] [AddSubgroupClass sigma A]
variable (graded : ℕ → sigma) [GradedRing graded]
variable (f : Proj graded ⟶ Spec (.of K)) [IsSeparated f]

/- The historical structure name is retained for compatibility with the
reduction wrappers; its fields deliberately describe the collision-aware
finite-flat families consumed by the arithmetic. -/
structure VoisinDegreeTenConfigurationCurveSteps
    (h : EffectiveZeroCycle (Proj graded)) : Prop where
  /-- The finite-flat family itself is retained, so its special fibers may be
  nonreduced (as required for `9 • h` and `4 • h`).  A map to the distinct
  configuration open cannot express those endpoint cycles. -/
  cubicResidualFamily : ∀ z : EffectiveZeroCycle (Proj graded),
    EffectiveZeroCycle.degree f z = 16 →
    ∃ F : RationalCycleFamily f, ∃ r : EffectiveZeroCycle (Proj graded),
      F.fiberCycle false = z + r ∧ F.fiberCycle true = 9 • h
  rankTwoResidualFamily : ∀ z : EffectiveZeroCycle (Proj graded),
    EffectiveZeroCycle.degree f z = 11 →
    ∃ F : RationalCycleFamily f, ∃ r : EffectiveZeroCycle (Proj graded),
      F.fiberCycle false = h + r ∧ F.fiberCycle true = z
  quadricResidualFamily : ∀ z : EffectiveZeroCycle (Proj graded),
    EffectiveZeroCycle.degree f z = 8 →
    ∃ F : RationalCycleFamily f, ∃ r : EffectiveZeroCycle (Proj graded),
      F.fiberCycle false = z + r ∧ F.fiberCycle true = 4 • h

/- A more concrete, split-cycle presentation keeps the parameter curves as
   maps to the full ordered relative powers.  The resulting disjoint-union
   family is collision-aware, so it can express repeated rational points at
   its endpoints.  Because its ordered coordinates are `K`-valued, it is
   strictly stronger than the point-specific degree-ten construction when
   Coray's closed point is non-split. -/
structure VoisinDegreeTenOrderedTupleCurveSteps
    (h : EffectiveZeroCycle (Proj graded)) : Prop where
  cubicResidualCurve : ∀ z : EffectiveZeroCycle (Proj graded),
    EffectiveZeroCycle.degree f z = 16 →
    ∃ (t : projectiveLineProj K ⟶ (orderedFamilyPowerOver f 16).left)
      (ht : t ≫ (orderedFamilyPowerOver f 16).hom = projectiveLineProjToBase K)
      (r : EffectiveZeroCycle (Proj graded)),
      (rationalCycleFamily_of_orderedTupleCurve graded f 16 t ht).fiberCycle false =
          z + r ∧
      (rationalCycleFamily_of_orderedTupleCurve graded f 16 t ht).fiberCycle true =
          9 • h
  rankTwoResidualCurve : ∀ z : EffectiveZeroCycle (Proj graded),
    EffectiveZeroCycle.degree f z = 11 →
    ∃ (t : projectiveLineProj K ⟶ (orderedFamilyPowerOver f 11).left)
      (ht : t ≫ (orderedFamilyPowerOver f 11).hom = projectiveLineProjToBase K)
      (r : EffectiveZeroCycle (Proj graded)),
      (rationalCycleFamily_of_orderedTupleCurve graded f 11 t ht).fiberCycle false =
          h + r ∧
      (rationalCycleFamily_of_orderedTupleCurve graded f 11 t ht).fiberCycle true =
          z
  quadricResidualCurve : ∀ z : EffectiveZeroCycle (Proj graded),
    EffectiveZeroCycle.degree f z = 8 →
    ∃ (t : projectiveLineProj K ⟶ (orderedFamilyPowerOver f 8).left)
      (ht : t ≫ (orderedFamilyPowerOver f 8).hom = projectiveLineProjToBase K)
      (r : EffectiveZeroCycle (Proj graded)),
      (rationalCycleFamily_of_orderedTupleCurve graded f 8 t ht).fiberCycle false =
          z + r ∧
      (rationalCycleFamily_of_orderedTupleCurve graded f 8 t ht).fiberCycle true =
          4 • h

theorem voisinDegreeTenConfigurationCurveSteps_of_orderedTupleCurveSteps
    (h : EffectiveZeroCycle (Proj graded))
    (curves : VoisinDegreeTenOrderedTupleCurveSteps (A := A) (K := K) graded f h) :
    VoisinDegreeTenConfigurationCurveSteps (A := A) (K := K) graded f h := by
  refine
    { cubicResidualFamily := ?_
      rankTwoResidualFamily := ?_
      quadricResidualFamily := ?_ }
  · intro z hz
    obtain ⟨t, ht, r, hzero, hinfinity⟩ := curves.cubicResidualCurve z hz
    exact ⟨rationalCycleFamily_of_orderedTupleCurve graded f 16 t ht, r,
      hzero, hinfinity⟩
  · intro z hz
    obtain ⟨t, ht, r, hzero, hinfinity⟩ := curves.rankTwoResidualCurve z hz
    exact ⟨rationalCycleFamily_of_orderedTupleCurve graded f 11 t ht, r,
      hzero, hinfinity⟩
  · intro z hz
    obtain ⟨t, ht, r, hzero, hinfinity⟩ := curves.quadricResidualCurve z hz
    exact ⟨rationalCycleFamily_of_orderedTupleCurve graded f 8 t ht, r,
      hzero, hinfinity⟩

lemma voisinDegreeTenFamilySteps_of_configurationCurveSteps
    (h : EffectiveZeroCycle (Proj graded))
    (curves : VoisinDegreeTenConfigurationCurveSteps (A := A) (K := K) graded f h) :
    VoisinDegreeTenFamilySteps f h := by
  exact
    { cubicResidualFamily := curves.cubicResidualFamily
      rankTwoResidualFamily := curves.rankTwoResidualFamily
      quadricResidualFamily := curves.quadricResidualFamily }

end AllCharacteristics.HomogeneousProjective

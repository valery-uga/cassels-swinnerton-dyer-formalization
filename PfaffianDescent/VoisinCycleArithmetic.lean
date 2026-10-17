import PfaffianDescent.CurveFamilyCycleQuotient
import PfaffianDescent.ResidualCurveFamily
import PfaffianDescent.ResidualCycles

/-!
# The cycle arithmetic in Voisin's degree-ten reduction

This file isolates the exact three geometric effectivity statements used in
the degree-ten case of Voisin's proof and checks their composition in the
actual quotient by finite-flat curve families.  The numerical chain is

`10 + 2·3 = 16`, `9·3 - 16 = 11`, `11 - 3 = 8`, and `4·3 - 8 = 4`.

The statements in `VoisinDegreeTenSteps` are deliberately about effectivity
of concrete cycle classes, rather than merely about integers.  Thus the
result below cannot be obtained from degree arithmetic alone: each of the
three residual representatives must be supplied by the corresponding
geometric construction.
-/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory AllCharacteristics
universe u

section
variable {K : Type u} [Field K] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of K)) [IsSeparated p]

/-- Scaling an effective cycle scales its scheme-theoretic degree. -/
lemma effectiveCycle_degree_nsmul (n : ℕ) (z : EffectiveZeroCycle X) :
    EffectiveZeroCycle.degree p (n • z) = n * EffectiveZeroCycle.degree p z := by
  induction n with
  | zero => simp [EffectiveZeroCycle.degree]
  | succ n ih =>
      rw [succ_nsmul, effectiveCycle_degree_add, ih, Nat.succ_mul]

/-- An exact effective-cycle decomposition gives Voisin's first residual
class once the complete intersection has the class of nine hyperplane
sections. The latter class identification is separate geometric work. -/
theorem effectiveCycleClass_firstResidual_of_cycle_add
    (h total residual input : EffectiveZeroCycle X)
    (hcycle : total = residual + input)
    (htotal : curveFamilyCycleClass p total.toZeroCycle =
      9 • curveFamilyCycleClass p h.toZeroCycle) :
    curveFamilyCycleClass p residual.toZeroCycle =
      9 • curveFamilyCycleClass p h.toZeroCycle -
        curveFamilyCycleClass p input.toZeroCycle := by
  have hclass := congrArg
    (fun z : EffectiveZeroCycle X => curveFamilyCycleClass p z.toZeroCycle) hcycle
  rw [effectiveCycleToSigned_add, map_add] at hclass
  exact eq_sub_of_add_eq (hclass.symm.trans htotal)

/- The numerical consequence of Voisin's quadratic effectivity statement.
The geometric input is that the class `3 [h] - [z]` is effective, where
`degree h = 3`; the representative then has degree `9 - degree z`.
This lemma deliberately keeps the effectivity certificate explicit, so it
does not package Voisin's geometric theorem as an axiom. -/
theorem effective_complement_degree_eq_nine_sub
    (h z r : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    {d : ℕ} (hz : EffectiveZeroCycle.degree p z = d)
    (hclass : curveFamilyCycleClass p r.toZeroCycle =
      3 • curveFamilyCycleClass p h.toZeroCycle -
        curveFamilyCycleClass p z.toZeroCycle) :
    EffectiveZeroCycle.degree p r = 9 - d := by
  have hdeg := effectiveRepresentative_degree_eq p r hclass
  simp only [curveFamilyCycleDegree_class, map_sub, map_nsmul,
    EffectiveZeroCycle.degree_toZeroCycle, hh, hz] at hdeg
  norm_num at hdeg
  have hnonneg : 0 ≤ (EffectiveZeroCycle.degree p r : ℤ) :=
    Int.natCast_nonneg _
  omega

theorem exists_effective_complement_degree_eq_nine_sub
    (h z : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    {d : ℕ} (hz : EffectiveZeroCycle.degree p z = d)
    (heff : CurveFamilyCycleQuotient.IsEffective p
      (3 • curveFamilyCycleClass p h.toZeroCycle -
        curveFamilyCycleClass p z.toZeroCycle)) :
    ∃ r : EffectiveZeroCycle X,
      EffectiveZeroCycle.degree p r = 9 - d := by
  obtain ⟨r, hclass⟩ := heff
  exact ⟨r, effective_complement_degree_eq_nine_sub p h z r hh hz hclass⟩

/-- The two residual degrees used in the paper follow immediately from the
quadratic effectivity class: degree five gives degree four, and degree four
gives degree five. -/
theorem exists_effective_degree_four_of_quadratic_effectivity
    (h z : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    (hz : EffectiveZeroCycle.degree p z = 5)
    (heff : CurveFamilyCycleQuotient.IsEffective p
      (3 • curveFamilyCycleClass p h.toZeroCycle -
        curveFamilyCycleClass p z.toZeroCycle)) :
    ∃ r : EffectiveZeroCycle X, EffectiveZeroCycle.degree p r = 4 := by
  obtain ⟨r, hr⟩ := exists_effective_complement_degree_eq_nine_sub
    p h z hh hz heff
  exact ⟨r, by simpa using hr⟩

theorem exists_effective_degree_five_of_quadratic_effectivity
    (h z : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    (hz : EffectiveZeroCycle.degree p z = 4)
    (heff : CurveFamilyCycleQuotient.IsEffective p
      (3 • curveFamilyCycleClass p h.toZeroCycle -
        curveFamilyCycleClass p z.toZeroCycle)) :
    ∃ r : EffectiveZeroCycle X, EffectiveZeroCycle.degree p r = 5 := by
  obtain ⟨r, hr⟩ := exists_effective_complement_degree_eq_nine_sub
    p h z hh hz heff
  exact ⟨r, by simpa using hr⟩

/- The rank-two residual family has degree `d - 3` when its input has
degree `d` and the fixed degree-three reference cycle has degree three. -/
theorem effective_subtraction_degree_eq_degree_sub_three
    (h z r : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    {d : ℕ} (hz : EffectiveZeroCycle.degree p z = d)
    (hclass : curveFamilyCycleClass p r.toZeroCycle =
      curveFamilyCycleClass p z.toZeroCycle -
        curveFamilyCycleClass p h.toZeroCycle) :
    EffectiveZeroCycle.degree p r = d - 3 := by
  have hdeg := effectiveRepresentative_degree_eq p r hclass
  simp only [curveFamilyCycleDegree_class, map_sub,
    EffectiveZeroCycle.degree_toZeroCycle, hz, hh] at hdeg
  have hnonneg : 0 ≤ (EffectiveZeroCycle.degree p r : ℤ) :=
    Int.natCast_nonneg _
  omega

/- The quadratic residual family has degree `12 - d` when its input has
degree `d` and the fixed degree-three reference cycle has degree three. -/
theorem effective_complement_degree_eq_twelve_sub
    (h z r : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    {d : ℕ} (hz : EffectiveZeroCycle.degree p z = d)
    (hclass : curveFamilyCycleClass p r.toZeroCycle =
      4 • curveFamilyCycleClass p h.toZeroCycle -
        curveFamilyCycleClass p z.toZeroCycle) :
    EffectiveZeroCycle.degree p r = 12 - d := by
  have hdeg := effectiveRepresentative_degree_eq p r hclass
  simp only [curveFamilyCycleDegree_class, map_sub, map_nsmul,
    EffectiveZeroCycle.degree_toZeroCycle, hh, hz] at hdeg
  norm_num at hdeg
  have hnonneg : 0 ≤ (EffectiveZeroCycle.degree p r : ℤ) :=
    Int.natCast_nonneg _
  omega

/-- The three effectivity constructions in the degree-ten part of Voisin's
argument.  Here `h` is the degree-three reference cycle selected by the
geometric construction.

* `cubicResidual` is Lemma 3.6 for `H = O_S(3)` and a length-sixteen cycle;
* `rankTwoResidual` is Proposition 3.2 for `(l,d,s) = (2,11,3)`;
* `quadricResidual` is Lemma 3.6 for `H = O_S(2)` and a length-eight cycle.
-/
structure VoisinDegreeTenSteps (h : EffectiveZeroCycle X) : Prop where
  cubicResidual : ∀ z : EffectiveZeroCycle X,
    EffectiveZeroCycle.degree p z = 16 →
      CurveFamilyCycleQuotient.IsEffective p
        (9 • curveFamilyCycleClass p h.toZeroCycle -
          curveFamilyCycleClass p z.toZeroCycle)
  rankTwoResidual : ∀ z : EffectiveZeroCycle X,
    EffectiveZeroCycle.degree p z = 11 →
      CurveFamilyCycleQuotient.IsEffective p
        (curveFamilyCycleClass p z.toZeroCycle -
          curveFamilyCycleClass p h.toZeroCycle)
  quadricResidual : ∀ z : EffectiveZeroCycle X,
    EffectiveZeroCycle.degree p z = 8 →
      CurveFamilyCycleQuotient.IsEffective p
        (4 • curveFamilyCycleClass p h.toZeroCycle -
          curveFamilyCycleClass p z.toZeroCycle)

/-- Concrete family data for the three degree-ten constructions.  The two
endpoint fibers encode the residual cycle directly; the resulting quotient
effectivity statements are proved below from the family relation. -/
structure VoisinDegreeTenFamilySteps (h : EffectiveZeroCycle X) : Prop where
  cubicResidualFamily : ∀ z : EffectiveZeroCycle X,
    EffectiveZeroCycle.degree p z = 16 →
      ∃ F : RationalCycleFamily p, ∃ r : EffectiveZeroCycle X,
        F.fiberCycle false = z + r ∧ F.fiberCycle true = 9 • h
  rankTwoResidualFamily : ∀ z : EffectiveZeroCycle X,
    EffectiveZeroCycle.degree p z = 11 →
      ∃ F : RationalCycleFamily p, ∃ r : EffectiveZeroCycle X,
        F.fiberCycle false = h + r ∧ F.fiberCycle true = z
  quadricResidualFamily : ∀ z : EffectiveZeroCycle X,
    EffectiveZeroCycle.degree p z = 8 →
      ∃ F : RationalCycleFamily p, ∃ r : EffectiveZeroCycle X,
        F.fiberCycle false = z + r ∧ F.fiberCycle true = 4 • h

/-- The point-specific form of the degree-ten argument.  Unlike
`VoisinDegreeTenFamilySteps`, this records only the three families actually
needed after Coray supplies one degree-ten point. -/
structure VoisinDegreeTenPointFamilySteps
    (h z₁₀ : EffectiveZeroCycle X) where
  cubicResidualFamily : RationalCycleFamily p
  residualEleven : EffectiveZeroCycle X
  cubicResidual_zero : cubicResidualFamily.fiberCycle false =
    z₁₀ + 2 • h + residualEleven
  cubicResidual_infinity : cubicResidualFamily.fiberCycle true = 9 • h
  rankTwoResidualFamily : RationalCycleFamily p
  residualEight : EffectiveZeroCycle X
  rankTwoResidual_zero : rankTwoResidualFamily.fiberCycle false = h + residualEight
  rankTwoResidual_infinity : rankTwoResidualFamily.fiberCycle true = residualEleven
  quadricResidualFamily : RationalCycleFamily p
  residualFour : EffectiveZeroCycle X
  quadricResidual_zero : quadricResidualFamily.fiberCycle false =
    residualEight + residualFour
  quadricResidual_infinity : quadricResidualFamily.fiberCycle true = 4 • h

/-- The quotient-level point-specific form of Voisin's degree-ten argument.
It records the three effective residual representatives and their actual
rational-equivalence classes.  This is the precise cycle-theoretic content
needed by the paper; a single endpoint family is a convenient strengthening
recorded separately by `VoisinDegreeTenPointFamilySteps`. -/
def VoisinDegreeTenPointSteps
    (h z₁₀ : EffectiveZeroCycle X) : Prop :=
  ∃ z₁₁ z₈ z₄ : EffectiveZeroCycle X,
    curveFamilyCycleClass p z₁₁.toZeroCycle =
      9 • curveFamilyCycleClass p h.toZeroCycle -
        curveFamilyCycleClass p (z₁₀ + 2 • h).toZeroCycle ∧
    curveFamilyCycleClass p z₈.toZeroCycle =
      curveFamilyCycleClass p z₁₁.toZeroCycle -
        curveFamilyCycleClass p h.toZeroCycle ∧
    curveFamilyCycleClass p z₄.toZeroCycle =
      4 • curveFamilyCycleClass p h.toZeroCycle -
        curveFamilyCycleClass p z₈.toZeroCycle

/-- Explicit endpoint families supply the quotient-level effectivity steps
used in the degree-ten cycle arithmetic. -/
theorem voisinDegreeTenSteps_of_familySteps
    (h : EffectiveZeroCycle X) (families : VoisinDegreeTenFamilySteps p h) :
    VoisinDegreeTenSteps p h := by
  refine
    { cubicResidual := ?_
      rankTwoResidual := ?_
      quadricResidual := ?_ }
  · intro z hz
    obtain ⟨F, r, hzero, hinfinity⟩ := families.cubicResidualFamily z hz
    exact residualClass_effective_of_rationalCycleFamily
      F z r h 9 hzero hinfinity
  · intro z hz
    obtain ⟨F, r, hzero, hinfinity⟩ := families.rankTwoResidualFamily z hz
    exact subtractionClass_effective_of_rationalCycleFamily
      F z r h hzero hinfinity
  · intro z hz
    obtain ⟨F, r, hzero, hinfinity⟩ := families.quadricResidualFamily z hz
    exact residualClass_effective_of_rationalCycleFamily
      F z r h 4 hzero hinfinity

/-- The first endpoint family in the point-specific construction has residual
degree eleven. -/
theorem voisinDegreeTenPointFamilySteps_residualEleven_degree
    (h z₁₀ : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10)
    (steps : VoisinDegreeTenPointFamilySteps p h z₁₀) :
    EffectiveZeroCycle.degree p steps.residualEleven = 11 := by
  have hd := steps.cubicResidualFamily.fiberCycle_degree_eq
  rw [steps.cubicResidual_zero, steps.cubicResidual_infinity,
    effectiveCycle_degree_add, effectiveCycle_degree_add,
    effectiveCycle_degree_nsmul, effectiveCycle_degree_nsmul, hz₁₀, hh] at hd
  norm_num at hd
  omega

/-- The rank-two endpoint family subtracts the degree-three reference cycle
from the preceding residual and therefore has degree eight. -/
theorem voisinDegreeTenPointFamilySteps_residualEight_degree
    (h z₁₀ : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10)
    (steps : VoisinDegreeTenPointFamilySteps p h z₁₀) :
    EffectiveZeroCycle.degree p steps.residualEight = 8 := by
  have h11 := voisinDegreeTenPointFamilySteps_residualEleven_degree
    p h z₁₀ hh hz₁₀ steps
  have hd := steps.rankTwoResidualFamily.fiberCycle_degree_eq
  rw [steps.rankTwoResidual_zero, steps.rankTwoResidual_infinity,
    effectiveCycle_degree_add, hh, h11] at hd
  omega

/-- The final cubic--quadric--quadric endpoint family has residual degree
four. -/
theorem voisinDegreeTenPointFamilySteps_residualFour_degree
    (h z₁₀ : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10)
    (steps : VoisinDegreeTenPointFamilySteps p h z₁₀) :
    EffectiveZeroCycle.degree p steps.residualFour = 4 := by
  have h8 := voisinDegreeTenPointFamilySteps_residualEight_degree
    p h z₁₀ hh hz₁₀ steps
  have hd := steps.quadricResidualFamily.fiberCycle_degree_eq
  rw [steps.quadricResidual_zero, steps.quadricResidual_infinity,
    effectiveCycle_degree_add, effectiveCycle_degree_nsmul, h8, hh] at hd
  norm_num at hd
  omega

/-- The three point-specific endpoint families produce the effective
degree-four cycle required to eliminate Coray's degree-ten alternative. -/
theorem effective_degree_four_of_voisin_degree_ten_point_family_steps
    (h z₁₀ : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10)
    (steps : VoisinDegreeTenPointFamilySteps p h z₁₀) :
    ∃ z₄ : EffectiveZeroCycle X, EffectiveZeroCycle.degree p z₄ = 4 := by
  exact ⟨steps.residualFour,
    voisinDegreeTenPointFamilySteps_residualFour_degree p h z₁₀ hh hz₁₀ steps⟩

/- The endpoint equations also determine the residual degrees, so the family
formulation carries the full `16 → 11 → 8 → 4` numerical chain. -/
theorem cubicResidualFamily_residual_degree
    (h : EffectiveZeroCycle X) (hh : EffectiveZeroCycle.degree p h = 3)
    (families : VoisinDegreeTenFamilySteps p h)
    (z : EffectiveZeroCycle X) (hz : EffectiveZeroCycle.degree p z = 16) :
    ∃ F : RationalCycleFamily p, ∃ r : EffectiveZeroCycle X,
      F.fiberCycle false = z + r ∧ F.fiberCycle true = 9 • h ∧
      EffectiveZeroCycle.degree p r = 11 := by
  obtain ⟨F, r, hzero, hinfinity⟩ := families.cubicResidualFamily z hz
  have hd := F.fiberCycle_degree_eq
  rw [hzero, hinfinity, effectiveCycle_degree_add,
    effectiveCycle_degree_nsmul, hz, hh] at hd
  norm_num at hd
  exact ⟨F, r, hzero, hinfinity, by omega⟩

theorem rankTwoResidualFamily_residual_degree
    (h : EffectiveZeroCycle X) (hh : EffectiveZeroCycle.degree p h = 3)
    (families : VoisinDegreeTenFamilySteps p h)
    (z : EffectiveZeroCycle X) (hz : EffectiveZeroCycle.degree p z = 11) :
    ∃ F : RationalCycleFamily p, ∃ r : EffectiveZeroCycle X,
      F.fiberCycle false = h + r ∧ F.fiberCycle true = z ∧
      EffectiveZeroCycle.degree p r = 8 := by
  obtain ⟨F, r, hzero, hinfinity⟩ := families.rankTwoResidualFamily z hz
  have hd := F.fiberCycle_degree_eq
  rw [hzero, hinfinity, effectiveCycle_degree_add, hz, hh] at hd
  exact ⟨F, r, hzero, hinfinity, by omega⟩

theorem quadricResidualFamily_residual_degree
    (h : EffectiveZeroCycle X) (hh : EffectiveZeroCycle.degree p h = 3)
    (families : VoisinDegreeTenFamilySteps p h)
    (z : EffectiveZeroCycle X) (hz : EffectiveZeroCycle.degree p z = 8) :
    ∃ F : RationalCycleFamily p, ∃ r : EffectiveZeroCycle X,
      F.fiberCycle false = z + r ∧ F.fiberCycle true = 4 • h ∧
      EffectiveZeroCycle.degree p r = 4 := by
  obtain ⟨F, r, hzero, hinfinity⟩ := families.quadricResidualFamily z hz
  have hd := F.fiberCycle_degree_eq
  rw [hzero, hinfinity, effectiveCycle_degree_add,
    effectiveCycle_degree_nsmul, hz, hh] at hd
  norm_num at hd
  exact ⟨F, r, hzero, hinfinity, by omega⟩

/-- Adding twice the degree-three reference cycle to a degree-ten cycle gives
the length-sixteen input for Voisin's first residual construction. -/
theorem effective_degree_sixteen_of_degree_ten_add_two_degree_three
    (h z₁₀ : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10) :
    EffectiveZeroCycle.degree p (z₁₀ + 2 • h) = 16 := by
  rw [effectiveCycle_degree_add, effectiveCycle_degree_nsmul, hz₁₀, hh]

/-- A uniform endpoint-family construction supplies the point-specific chain
used after Coray has selected one degree-ten point.  This keeps the older
uniform interface interoperable with the exact, weaker interface without
reintroducing a geometric assumption. -/
theorem nonempty_voisinDegreeTenPointFamilySteps_of_familySteps
    (h z₁₀ : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    (families : VoisinDegreeTenFamilySteps p h)
    (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10) :
    Nonempty (VoisinDegreeTenPointFamilySteps p h z₁₀) := by
  let z₁₆ : EffectiveZeroCycle X := z₁₀ + 2 • h
  have hz₁₆ : EffectiveZeroCycle.degree p z₁₆ = 16 := by
    dsimp [z₁₆]
    exact effective_degree_sixteen_of_degree_ten_add_two_degree_three p h z₁₀ hh hz₁₀
  obtain ⟨F₁₆, z₁₁, hzero₁₆, hinfinity₁₆, hz₁₁⟩ :=
    cubicResidualFamily_residual_degree p h hh families z₁₆ hz₁₆
  obtain ⟨F₁₁, z₈, hzero₁₁, hinfinity₁₁, hz₈⟩ :=
    rankTwoResidualFamily_residual_degree p h hh families z₁₁ hz₁₁
  obtain ⟨F₈, z₄, hzero₈, hinfinity₈, _⟩ :=
    quadricResidualFamily_residual_degree p h hh families z₈ hz₈
  refine ⟨?_⟩
  refine
    { cubicResidualFamily := F₁₆
      residualEleven := z₁₁
      cubicResidual_zero := ?_
      cubicResidual_infinity := hinfinity₁₆
      rankTwoResidualFamily := F₁₁
      residualEight := z₈
      rankTwoResidual_zero := hzero₁₁
      rankTwoResidual_infinity := hinfinity₁₁
      quadricResidualFamily := F₈
      residualFour := z₄
      quadricResidual_zero := hzero₈
      quadricResidual_infinity := hinfinity₈ }
  simpa [z₁₆] using hzero₁₆

/-- A concrete three-family chain determines the quotient-level
rational-equivalence chain used in the degree-ten argument. -/
theorem voisinDegreeTenPointSteps_of_familySteps
    (h z₁₀ : EffectiveZeroCycle X)
    (steps : VoisinDegreeTenPointFamilySteps p h z₁₀) :
    VoisinDegreeTenPointSteps p h z₁₀ := by
  refine ⟨steps.residualEleven, steps.residualEight, steps.residualFour, ?_, ?_, ?_⟩
  · have hc := curveFamilyCycleClass_fibers p steps.cubicResidualFamily
    rw [steps.cubicResidual_zero, steps.cubicResidual_infinity,
      effectiveCycleToSigned_add, effectiveCycleToSigned_nsmul, map_add, map_nsmul] at hc
    apply (eq_sub_iff_add_eq).2
    rw [add_comm]
    exact hc
  · have hc := curveFamilyCycleClass_fibers p steps.rankTwoResidualFamily
    rw [steps.rankTwoResidual_zero, steps.rankTwoResidual_infinity,
      effectiveCycleToSigned_add, map_add] at hc
    apply (eq_sub_iff_add_eq).2
    rw [add_comm]
    exact hc
  · have hc := curveFamilyCycleClass_fibers p steps.quadricResidualFamily
    rw [steps.quadricResidual_zero, steps.quadricResidual_infinity,
      effectiveCycleToSigned_add, effectiveCycleToSigned_nsmul, map_add, map_nsmul] at hc
    apply (eq_sub_iff_add_eq).2
    rw [add_comm]
    exact hc

/-- The quotient-level point-specific chain produces the effective
degree-four cycle which eliminates Coray's degree-ten branch. -/
theorem effective_degree_four_of_voisin_degree_ten_point_steps
    (h z₁₀ : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree p h = 3)
    (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10)
    (steps : VoisinDegreeTenPointSteps p h z₁₀) :
    ∃ z₄ : EffectiveZeroCycle X, EffectiveZeroCycle.degree p z₄ = 4 := by
  obtain ⟨z₁₁, z₈, z₄, hz₁₁class, hz₈class, hz₄class⟩ := steps
  have hz₁₆ : EffectiveZeroCycle.degree p (z₁₀ + 2 • h) = 16 :=
    effective_degree_sixteen_of_degree_ten_add_two_degree_three p h z₁₀ hh hz₁₀
  have hz₁₁ : EffectiveZeroCycle.degree p z₁₁ = 11 := by
    have hd := effectiveRepresentative_degree_eq p z₁₁ hz₁₁class
    simp only [map_sub, map_nsmul, curveFamilyCycleDegree_class,
      EffectiveZeroCycle.degree_toZeroCycle, hh, hz₁₆] at hd
    norm_num at hd
    omega
  have hz₈ : EffectiveZeroCycle.degree p z₈ = 8 := by
    have hd := effectiveRepresentative_degree_eq p z₈ hz₈class
    simp only [map_sub, curveFamilyCycleDegree_class,
      EffectiveZeroCycle.degree_toZeroCycle, hz₁₁, hh] at hd
    omega
  refine ⟨z₄, ?_⟩
  have hd := effectiveRepresentative_degree_eq p z₄ hz₄class
  simp only [map_sub, map_nsmul, curveFamilyCycleDegree_class,
    EffectiveZeroCycle.degree_toZeroCycle, hh, hz₈] at hd
  norm_num at hd
  omega

/-- Voisin's three geometric constructions turn every effective degree-ten
cycle into an effective degree-four cycle.  All intermediate degrees are
deduced from equality in the actual curve-family quotient. -/
theorem effective_degree_four_of_voisin_degree_ten_steps
    (h : EffectiveZeroCycle X) (hh : EffectiveZeroCycle.degree p h = 3)
    (steps : VoisinDegreeTenSteps p h)
    (z₁₀ : EffectiveZeroCycle X) (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10) :
    ∃ z₄ : EffectiveZeroCycle X, EffectiveZeroCycle.degree p z₄ = 4 := by
  let z₁₆ : EffectiveZeroCycle X := z₁₀ + 2 • h
  have hz₁₆ : EffectiveZeroCycle.degree p z₁₆ = 16 := by
    dsimp [z₁₆]
    exact effective_degree_sixteen_of_degree_ten_add_two_degree_three p h z₁₀ hh hz₁₀
  obtain ⟨z₁₁, hz₁₁class⟩ := steps.cubicResidual z₁₆ hz₁₆
  have hz₁₁ : EffectiveZeroCycle.degree p z₁₁ = 11 := by
    have hd := effectiveRepresentative_degree_eq p z₁₁ hz₁₁class
    simp only [map_sub, map_nsmul, curveFamilyCycleDegree_class,
      EffectiveZeroCycle.degree_toZeroCycle, hh, hz₁₆] at hd
    norm_num at hd
    omega
  obtain ⟨z₈, hz₈class⟩ := steps.rankTwoResidual z₁₁ hz₁₁
  have hz₈ : EffectiveZeroCycle.degree p z₈ = 8 := by
    have hd := effectiveRepresentative_degree_eq p z₈ hz₈class
    simp only [map_sub, curveFamilyCycleDegree_class,
      EffectiveZeroCycle.degree_toZeroCycle, hz₁₁, hh] at hd
    omega
  obtain ⟨z₄, hz₄class⟩ := steps.quadricResidual z₈ hz₈
  refine ⟨z₄, ?_⟩
  have hd := effectiveRepresentative_degree_eq p z₄ hz₄class
  simp only [map_sub, map_nsmul, curveFamilyCycleDegree_class,
    EffectiveZeroCycle.degree_toZeroCycle, hh, hz₈] at hd
  norm_num at hd
  omega

/-- The endpoint-family formulation directly yields the degree-four cycle,
without making callers unpack the intermediate quotient-level steps. -/
theorem effective_degree_four_of_voisin_degree_ten_family_steps
    (h : EffectiveZeroCycle X) (hh : EffectiveZeroCycle.degree p h = 3)
    (families : VoisinDegreeTenFamilySteps p h)
    (z₁₀ : EffectiveZeroCycle X)
    (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10) :
    ∃ z₄ : EffectiveZeroCycle X, EffectiveZeroCycle.degree p z₄ = 4 := by
  exact effective_degree_four_of_voisin_degree_ten_steps p h hh
    (voisinDegreeTenSteps_of_familySteps p h families) z₁₀ hz₁₀

/- The family-level API can expose the complete numerical chain in one
statement.  This is useful to callers that need to retain the intermediate
cycles for subsequent geometric constructions. -/
theorem voisinDegreeTenFamilySteps_degree_chain
    (h : EffectiveZeroCycle X) (hh : EffectiveZeroCycle.degree p h = 3)
    (families : VoisinDegreeTenFamilySteps p h)
    (z₁₀ : EffectiveZeroCycle X)
    (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10) :
    ∃ z₁₆ z₁₁ z₈ z₄ : EffectiveZeroCycle X,
      EffectiveZeroCycle.degree p z₁₆ = 16 ∧
      EffectiveZeroCycle.degree p z₁₁ = 11 ∧
      EffectiveZeroCycle.degree p z₈ = 8 ∧
      EffectiveZeroCycle.degree p z₄ = 4 := by
  let z₁₆ : EffectiveZeroCycle X := z₁₀ + 2 • h
  have hz₁₆ : EffectiveZeroCycle.degree p z₁₆ = 16 := by
    dsimp [z₁₆]
    exact effective_degree_sixteen_of_degree_ten_add_two_degree_three p h z₁₀ hh hz₁₀
  obtain ⟨_, z₁₁, _, _, hz₁₁⟩ := cubicResidualFamily_residual_degree
    p h hh families z₁₆ hz₁₆
  obtain ⟨_, z₈, _, _, hz₈⟩ := rankTwoResidualFamily_residual_degree
    p h hh families z₁₁ hz₁₁
  obtain ⟨_, z₄, _, _, hz₄⟩ := quadricResidualFamily_residual_degree
    p h hh families z₈ hz₈
  exact ⟨z₁₆, z₁₁, z₈, z₄, hz₁₆, hz₁₁, hz₈, hz₄⟩

/- The same chain can retain the actual endpoint families and residual cycles.
This is the data needed by the geometric assembly step, where the numerical
degrees alone are insufficient. -/
theorem voisinDegreeTenFamilySteps_chain_data
    (h : EffectiveZeroCycle X) (hh : EffectiveZeroCycle.degree p h = 3)
    (families : VoisinDegreeTenFamilySteps p h)
    (z₁₀ : EffectiveZeroCycle X)
    (hz₁₀ : EffectiveZeroCycle.degree p z₁₀ = 10) :
    ∃ z₁₆ z₁₁ z₈ z₄ : EffectiveZeroCycle X,
      EffectiveZeroCycle.degree p z₁₆ = 16 ∧
      EffectiveZeroCycle.degree p z₁₁ = 11 ∧
      EffectiveZeroCycle.degree p z₈ = 8 ∧
      EffectiveZeroCycle.degree p z₄ = 4 ∧
      (∃ F₁₆ : RationalCycleFamily p, ∃ r₁₆ : EffectiveZeroCycle X,
        F₁₆.fiberCycle false = z₁₆ + r₁₆ ∧
        F₁₆.fiberCycle true = 9 • h ∧
        r₁₆ = z₁₁) ∧
      (∃ F₁₁ : RationalCycleFamily p, ∃ r₁₁ : EffectiveZeroCycle X,
        F₁₁.fiberCycle false = h + r₁₁ ∧
        F₁₁.fiberCycle true = z₁₁ ∧
        r₁₁ = z₈) ∧
      (∃ F₈ : RationalCycleFamily p, ∃ r₈ : EffectiveZeroCycle X,
        F₈.fiberCycle false = z₈ + r₈ ∧
        F₈.fiberCycle true = 4 • h ∧
        r₈ = z₄) := by
  let z₁₆ : EffectiveZeroCycle X := z₁₀ + 2 • h
  have hz₁₆ : EffectiveZeroCycle.degree p z₁₆ = 16 := by
    dsimp [z₁₆]
    exact effective_degree_sixteen_of_degree_ten_add_two_degree_three p h z₁₀ hh hz₁₀
  obtain ⟨F₁₆, r₁₆, hzero₁₆, hinfinity₁₆, hr₁₆⟩ :=
    cubicResidualFamily_residual_degree p h hh families z₁₆ hz₁₆
  obtain ⟨F₁₁, r₁₁, hzero₁₁, hinfinity₁₁, hr₁₁⟩ :=
    rankTwoResidualFamily_residual_degree p h hh families r₁₆ hr₁₆
  obtain ⟨F₈, r₈, hzero₈, hinfinity₈, hr₈⟩ :=
    quadricResidualFamily_residual_degree p h hh families r₁₁ hr₁₁
  refine ⟨z₁₆, r₁₆, r₁₁, r₈, hz₁₆, hr₁₆, hr₁₁, hr₈, ?_, ?_, ?_⟩
  · exact ⟨F₁₆, r₁₆, hzero₁₆, hinfinity₁₆, rfl⟩
  · exact ⟨F₁₁, r₁₁, hzero₁₁, hinfinity₁₁, rfl⟩
  · exact ⟨F₈, r₈, hzero₈, hinfinity₈, rfl⟩

end
end PfaffianDescent

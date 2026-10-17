import PfaffianDescent.CorayNativeLocalizedProjectiveHyperplanePullback
import PfaffianDescent.CorayBoundedOriginalChartEvaluation
import PfaffianDescent.CorayOriginalChartGenericLinearity

/-! ORIGINAL bounded section basis yields SAME-degree through-point member and
its literal hyperplane pullback on the native denominator-nonzero open. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Every NONZERO original-K hyperplane coefficient vector produces its
literal degree-n polynomial q through the SAME original coordinates, nonzero
modulo p. The full native hyperplane equation pulls back to normalized q
multiplied by the inverse of the actual basis coordinate. This proves only
the needed local map/equation dictionary, not image dimension/reducibility. -/
theorem cubicThroughPointBasis_nativeLocalizedHyperplane_exists_originalMember001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) (c : Fin m → K) (hc : c ≠ 0) :
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let x := fun i => e (b i)
    x a ≠ 0 ∧ ∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous n ∧ q.eval₂ (algebraMap K L) y = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = (∑ i, c i • b i).1.1 ∧
      nativeLocalizedProjectiveChartMap (chartBaseMap (equationIdeal p hp) j) x a
        (projectiveChartLinearForm a c) =
          algebraMap (ChartRing (equationIdeal p hp) j) (Localization.Away (x a))
            (e (∑ i, c i • b i)) * IsLocalization.Away.invSelf (x a) ∧
      (∀ T : Ideal (Localization.Away (x a)),
        nativeLocalizedProjectiveChartMap (chartBaseMap (equationIdeal p hp) j) x a
            (projectiveChartLinearForm a c) ∈ T ↔
          algebraMap (ChartRing (equationIdeal p hp) j) (Localization.Away (x a))
            (e (∑ i, c i • b i)) ∈ T) := by
  classical
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let x := fun i => e (b i)
  let s : cubicThroughCoordinateSections p hp n y hpy := ∑ i, c i • b i
  have hSum : e s = ∑ i, c i • e (b i) := by simp only [s, map_sum, map_smul]
  have hNumerator : (∑ i, chartBaseMap (equationIdeal p hp) j (c i) * x i) = e s := by
    rw [hSum]
    apply Finset.sum_congr rfl
    intro i _
    exact (gradedChartNative_smul_eq_baseMap_mul (grading (equationIdeal p hp))
      (c i) (e (b i))).symm
  have hNonzero : s ≠ 0 := by
    intro h
    apply hc
    apply (cubicThroughPointChartBasis_relation_iff p hp hp0 n y hpy j b c).mp
    rw [← hSum, h, map_zero]
  obtain ⟨q, hq, hy, hqS⟩ :=
    (cubicThroughCoordinateSections_mem_iff p hp n y hpy s.1).mp s.2
  have hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro h
    have hqZero : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h
    have hsZero : s.1.1 = 0 := hqS.symm.trans hqZero
    apply hNonzero
    apply Subtype.ext
    apply Subtype.ext
    exact hsZero
  have hDenominator : x a ≠ 0 := by
    change e (b a) ≠ 0
    intro hZero
    apply b.ne_zero a
    have hEq : e (b a) = e 0 := hZero.trans (map_zero e).symm
    exact (cubicThroughPointChartEvaluation_injective p hp hp0 n y hpy j) hEq
  have hData := nativeLocalizedProjectiveChartMap_hyperplane_pullback001
    (chartBaseMap (equationIdeal p hp) j) x a
  have hForm := hData.2.2.1 c
  rw [hNumerator] at hForm
  refine ⟨hDenominator, q, hq, hy, hnot, hqS, hForm, ?_⟩
  intro T
  have h := hData.2.2.2 c T
  rw [hNumerator] at h
  exact h

end PfaffianDescent.Coray

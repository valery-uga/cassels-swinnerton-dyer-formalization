import PfaffianDescent.CorayRelevantPrimeComponentHyperplaneDegree
import PfaffianDescent.ProjectiveChartRegularOfCoordinateRegular
import PfaffianDescent.QuotientChartKernel
import PfaffianDescent.VoisinRegularPrincipalProjectiveCharts
import AllCharacteristics.FiniteSchemeCycle

/-! SAME actual hyperplane section: derive its native regular-principal
immersion into the selected component and identify its fundamental-cycle
degree with the OWN coordinate Hilbert degree. No regularity, Cartier or
degree comparison premise is supplied to the selected-component caller.
This is the hyperplane divisor ON C; C as divisor on the cubic, its global
intersection pairing and adjunction remain distinct. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Literal H not in the prime C derives regularity of its coordinate class,
regularity on EVERY actual chart, the actual principal chart kernel, and thus
an effective-Cartier presentation of the SAME hyperplane quotient immersion. -/
noncomputable def primeComponent_linearSection_regularPrincipalImmersion
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [C.toIdeal.IsPrime]
    (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1) (hnot : H ∉ C.toIdeal) :
    PfaffianDescent.RegularPrincipalImmersion
      (PfaffianDescent.schemeQuotientMap C (C ⊔ equationIdeal H hH) le_sup_left) := by
  let s : grading C 1 :=
    ⟨Ideal.Quotient.mk C.toIdeal H, polynomial_class_mem_grading C H hH⟩
  have hs : IsRegular (s : CoordinateRing C) := isRegular_iff_ne_zero.mpr (by
    intro hz
    exact hnot (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hcharts : PfaffianDescent.HasRegularPrincipalStandardCharts
      C (C ⊔ equationIdeal H hH) le_sup_left := by
    intro j
    refine ⟨H.eval₂ (chartBaseMap C j) (chartCoordinate C j), ?_, ?_⟩
    · rw [eval₂_chartCoordinate_eq_fraction C j H hH]
      exact PfaffianDescent.chartSection_isRegular_of_coordinateRing_isRegular C s hs j
    · exact PfaffianDescent.chartQuotientMap_ker_eq_equation C H hH j
  exact hcharts.toImmersion

/-- Construct the SAME actual finite hyperplane Cartier divisor on the actual
prime component, with its OWN fundamental-cycle degree equal to the component's
intrinsic Hilbert degree, bounded by3n. The actual Cartier presentation, finite
section, cycle and comparison are derived; all original-K residue degrees and
scheme multiplicities are retained. -/
theorem selectedProjectiveRelevantPrime_exists_hyperplaneCartierCycle_degree
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [C.toIdeal.IsPrime]
    (hCrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C)
    (hPQC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal) :
    ∃ (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1), H ∉ C.toIdeal ∧
      ∃ hfinite : IsFinite (toBase (C ⊔ equationIdeal H hH)),
        letI := hfinite
        let i := PfaffianDescent.schemeQuotientMap C (C ⊔ equationIdeal H hH) le_sup_left
        letI := PfaffianDescent.schemeQuotientMap_closedImmersion C (C ⊔ equationIdeal H hH) le_sup_left
        Nonempty (PfaffianDescent.RegularPrincipalImmersion i) ∧
          ∃ zS : EffectiveZeroCycle (scheme (C ⊔ equationIdeal H hH)),
            EffectiveZeroCycle.degree (toBase C) (pushforwardClosedCycle i zS) =
                actualCurveCoordinateHilbertDegree C ∧
              actualCurveCoordinateHilbertDegree C ≤ 3 * n := by
  classical
  obtain ⟨H, hH, hnotC, hfinite, hdegree, hbound, _N, _hN⟩ :=
    selectedProjectiveRelevantPrime_exists_hyperplane_degree_bound
      p q hp hp0 n hq hnot C hCrel hPQC
  let S := C ⊔ equationIdeal H hH
  letI : IsFinite (toBase S) := hfinite
  let i := PfaffianDescent.schemeQuotientMap C S le_sup_left
  letI : IsClosedImmersion i := PfaffianDescent.schemeQuotientMap_closedImmersion C S le_sup_left
  have hbase : i ≫ toBase C = toBase S := PfaffianDescent.schemeQuotientMap_toBase C S le_sup_left
  obtain ⟨zS, hzS⟩ := exists_effectiveZeroCycle_degree_finiteSchemeRank (toBase S)
  refine ⟨H, hH, hnotC, hfinite,
    ⟨primeComponent_linearSection_regularPrincipalImmersion C H hH hnotC⟩, zS, ?_, hbound⟩
  rw [degree_pushforwardClosedCycle, hbase, hzS]
  exact hdegree.symm

end PfaffianDescent.Coray

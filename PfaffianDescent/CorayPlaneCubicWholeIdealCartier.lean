import PfaffianDescent.CorayNonzeroIdealRegularCurve
import PfaffianDescent.CorayPlaneCubicChartRegularCurve
import PfaffianDescent.CorayHomogeneousChartKernelNonzero
import PfaffianDescent.VoisinFixedCurveLocalUFDImmersion

/-! SOURCE ONLY / UNCOMPILED156. Whole arbitrary nonradical homogeneous ideals
in a smooth integral plane cubic have Cartier immersion once an actual surviving
homogeneous member is constructed. The original-input caller supplies that
member from actual whole-cut finiteness/Hilbert growth, never as a final premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ENTIRE actual chart kernels have regular principal equations on a
basic open cover; thickening is retained because no prime-kernel hypothesis
or radical replacement occurs. -/
theorem planeCubicWholeIdeal_hasStalkwiseRegularPrincipalStandardCharts
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 3) K))).IsPrime)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 3) K))
    (hIJ : (equationIdeal p hp).toIdeal ≤ J.toIdeal)
    (f : MvPolynomial (Fin 3) K) {d : ℕ} (hf : f.IsHomogeneous d)
    (hfJ : f ∈ J.toIdeal) (hfI : f ∉ (equationIdeal p hp).toIdeal) :
    PfaffianDescent.HasStalkwiseRegularPrincipalStandardCharts
      (equationIdeal p hp) J hIJ := by
  let I := equationIdeal p hp
  letI : IsDomain (CoordinateRing I) :=
    (Ideal.Quotient.isDomain_iff_prime I.toIdeal).mpr hprime
  intro j Q _
  letI : IsDomain (ChartRing I j) := planeCubic_chartRing_isDomain p hp hp0 hprime j
  letI : IsRegularRing (ChartRing I j) := planeCubic_chartRing_isRegularRing p hp j
  have hj : coordinate I j ≠ 0 := by
    intro hzero
    have hdiv : p ∣ X j :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv (X_ne_zero j)
    rw [hp.totalDegree hp0, MvPolynomial.totalDegree_X] at hle
    omega
  have hkernel := chartQuotientMap_ker_ne_bot_of_surviving_homogeneous_member
    I J hIJ j hj f hf hfJ hfI
  exact regularDomain_nonzeroIdeal_basicOpen_regularPrincipal
    (planeCubic_chartRing_ringKrullDim_le_one p hp hp0 j)
    (RingHom.ker (PfaffianDescent.chartQuotientMap I J hIJ j)) hkernel Q

/-- Native affine refinements assemble into the ACTUAL projective quotient
immersion, using the complete chart kernels and actual Cartesian squares. -/
def planeCubicWholeIdeal_regularPrincipalImmersion
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 3) K))).IsPrime)
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 3) K))
    (hIJ : (equationIdeal p hp).toIdeal ≤ J.toIdeal)
    (f : MvPolynomial (Fin 3) K) {d : ℕ} (hf : f.IsHomogeneous d)
    (hfJ : f ∈ J.toIdeal) (hfI : f ∉ (equationIdeal p hp).toIdeal) :
    PfaffianDescent.RegularPrincipalImmersion
      (PfaffianDescent.schemeQuotientMap (equationIdeal p hp) J hIJ) :=
  (planeCubicWholeIdeal_hasStalkwiseRegularPrincipalStandardCharts
    p hp hp0 hprime J hIJ f hf hfJ hfI).toImmersion

end PfaffianDescent.Coray

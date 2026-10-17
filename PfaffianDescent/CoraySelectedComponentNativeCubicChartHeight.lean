import PfaffianDescent.CorayHomogeneousMinimalPrimeNativeChart
import PfaffianDescent.CoraySelectedComponentHeightAndRelevance
import PfaffianDescent.QuotientChartKernel
import PfaffianDescent.VoisinSmoothCubicChartLocalRegularity
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# The selected component has native cubic-chart height one

Homogeneous height two supplies projective relevance. Actual chart
component minimality supplies the principal-ideal height upper bound.
Original q nonmembership supplies the lower bound in the SAME cubic chart.
No desired height, principal generation or Cartier premise is supplied.
SOURCE ONLY / UNVERIFIED; root owns all compiler and audit checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A selected homogeneous equation outside the original cubic ideal stays
nonzero in EVERY actual native cubic chart, for arbitrary homogeneous degree. -/
theorem selectedHomogeneousEquation_nativeCubicChart_ne_zero
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (j : Fin 4) :
    q.eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j) ≠ 0 := by
  let I := equationIdeal p hp
  letI : IsDomain (CoordinateRing I) :=
    (Ideal.Quotient.isDomain_iff_prime I.toIdeal).mpr
      (PfaffianDescent.principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  have hz : coordinate I j ≠ 0 := by
    intro hzero
    exact PfaffianDescent.coordinate_not_mem_cubic_ideal p hp hp0 j
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  let M := Submonoid.powers (coordinate I j)
  have hM : M ≤ nonZeroDivisors (CoordinateRing I) := by
    intro x hx
    obtain ⟨d, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero d hz)
  intro hzero
  have hfrac0 : Away.mk (grading I) (coordinate_mem I j) n
      (Ideal.Quotient.mk I.toIdeal q)
      (by simpa using polynomial_class_mem_grading I q hq) = 0 := by
    rw [← eval₂_chartCoordinate_eq_fraction I j q hq]
    exact hzero
  have hval := congrArg HomogeneousLocalization.val hfrac0
  simp only [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_eq_mk'] at hval
  obtain ⟨m, hm⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hval
  have hmne : (m : CoordinateRing I) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (hM m.property)
  have hqzero : Ideal.Quotient.mk I.toIdeal q = 0 :=
    (mul_eq_zero.mp hm).resolve_left hmne
  exact hnot (Ideal.Quotient.eq_zero_iff_mem.mp hqzero)

/-- The OWN canonical selected-component kernel in the original smooth
cubic chart is top (empty chart), or a prime of height exactly one.
The auxiliary p-membership proof affects no map by proof irrelevance. -/
theorem selectedProjectiveMinimalComponent_nativeCubicChartKernel_top_or_heightOne
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hCp : p ∈ C.toIdeal) (j : Fin 4) :
    let P := PfaffianDescent.fixedCurveCubicChartKernel p hp C hCp j
    P = ⊤ ∨ (P.IsPrime ∧ P.height = 1) := by
  let H := equationIdeal p hp
  let I := projectiveIntersectionIdeal p q hp hq
  have hHI : H.toIdeal ≤ I.toIdeal := by
    change (equationIdeal p hp).toIdeal ≤
      (equationIdeal p hp ⊔ equationIdeal q hq).toIdeal
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_left
  have hHC := equationIdeal_le_homogeneousIdeal_of_mem hp hCp
  let f := chartQuotientMap H I hHI j
  let g := chartQuotientMap I C hCmin.le j
  let h := chartQuotientMap H C hHC j
  have hcomp : g.comp f = h := chartQuotientMap_comp H I hHI C hCmin.le hHC j
  have hkercomp : (RingHom.ker g).comap f = RingHom.ker h := by
    rw [RingHom.comap_ker, hcomp]
  rcases homogeneousMinimalPrime_nativeChartKernel_top_or_minimalPrime I C hCmin
      (selectedProjectiveMinimalComponent_homogeneous_relevant
        p q hp hp0 n hq hnot C hCmin) j with htop | ⟨hprime, hminimal⟩
  · left
    change RingHom.ker h = ⊤
    rw [← hkercomp, htop, Ideal.comap_top]
  · letI : IsDomain (ChartRing H j) :=
      PfaffianDescent.smoothCubic_chartRing_isDomain p hp hp0 j
    letI : IsRegularRing (ChartRing H j) :=
      PfaffianDescent.smoothCubic_chartRing_isRegularRing p hp j
    have hmin : RingHom.ker h ∈ (RingHom.ker f).minimalPrimes := by
      have hcomap := Ideal.minimalPrimes_comap_of_surjective
        (chartQuotientMap_surjective H I hHI j) hminimal
      rw [← RingHom.ker_eq_comap_bot, hkercomp] at hcomap
      exact hcomap
    let s := q.eval₂ (chartBaseMap H j) (chartCoordinate H j)
    have hker : RingHom.ker f = Ideal.span ({s} : Set (ChartRing H j)) :=
      PfaffianDescent.chartQuotientMap_ker_eq_equation H q hq j
    have hminS : RingHom.ker h ∈ (Ideal.span ({s} : Set (ChartRing H j))).minimalPrimes := by
      rw [← hker]
      exact hmin
    have hprimeH : (RingHom.ker h).IsPrime := hminS.isPrime
    have hupper : (RingHom.ker h).height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hminS
    have hlower : 1 ≤ (RingHom.ker h).height :=
      (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr
          (selectedHomogeneousEquation_nativeCubicChart_ne_zero p q hp hp0 n hq hnot j))).trans
        (Ideal.height_mono hminS.le)
    exact Or.inr ⟨hprimeH, le_antisymm hupper hlower⟩

end PfaffianDescent.Coray

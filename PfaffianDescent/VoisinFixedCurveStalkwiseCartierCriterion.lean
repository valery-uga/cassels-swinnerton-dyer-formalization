import PfaffianDescent.VoisinHeightOnePrimeDenseOpenCartier
import PfaffianDescent.VoisinHomogeneousIdealGenericSpreading
import PfaffianDescent.VoisinDegreeEightFixedCurveScheme
import PfaffianDescent.VoisinSmoothCubicChartDomain

/-!
# Stalkwise local factoriality and the fixed-curve Cartier equation

The standard affine charts of a smooth cubic surface need not be factorial.
For a Cartier curve, factoriality is required only in local rings at points
on the curve. A finite-generation argument spreads each stalk generator to
a principal equation on a basic open containing that point.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A regular principal equation for a finitely generated ideal at one prime
spreads to a regular principal equation on one basic open around that prime.
The local generator is represented by an actual element of the original ideal,
and all denominators are cleared simultaneously. -/
theorem ideal_localRegularPrincipal_spreads_to_basicOpen
    {A : Type u} [CommRing A] [IsDomain A]
    (I Q : Ideal A) [Q.IsPrime] (hfg : I.FG)
    (hprincipal : ∃ a : Localization.AtPrime Q,
      IsRegular a ∧
      I.map (algebraMap A (Localization.AtPrime Q)) =
        Ideal.span ({a} : Set (Localization.AtPrime Q))) :
    ∃ s : A, s ∉ Q ∧ ∃ z : A, z ∈ I ∧
      IsRegular (algebraMap A (Localization.Away s) z) ∧
      I.map (algebraMap A (Localization.Away s)) =
        Ideal.span ({algebraMap A (Localization.Away s) z} :
          Set (Localization.Away s)) := by
  classical
  let S := Localization.AtPrime Q
  obtain ⟨a, haRegular, haI⟩ := hprincipal
  have haMem : a ∈ I.map (algebraMap A S) := by
    rw [haI]
    exact Ideal.mem_span_singleton_self a
  obtain ⟨⟨⟨z, hzI⟩, d⟩, hzd⟩ :=
    (IsLocalization.mem_map_algebraMap_iff Q.primeCompl S).mp haMem
  have hdUnit : IsUnit (algebraMap A S (d : A)) :=
    IsLocalization.map_units S d
  have hlocEq : I.map (algebraMap A S) =
      Ideal.span ({algebraMap A S z} : Set S) := by
    calc
      I.map (algebraMap A S) = Ideal.span ({a} : Set S) := haI
      _ = Ideal.span ({a * algebraMap A S (d : A)} : Set S) :=
        (Ideal.span_singleton_mul_right_unit hdUnit a).symm
      _ = Ideal.span ({algebraMap A S z} : Set S) := by rw [hzd]
  have hle : I.map (algebraMap A S) ≤
      (Ideal.span ({z} : Set A)).map (algebraMap A S) := by
    simpa only [Ideal.map_span, Set.image_singleton] using le_of_eq hlocEq
  obtain ⟨s, hsQ, hleAway⟩ :=
    exists_away_ideal_le_of_atPrime_le_of_fg
      Q I (Ideal.span ({z} : Set A)) hfg hle
  have hAwayEq : I.map (algebraMap A (Localization.Away s)) =
      Ideal.span ({algebraMap A (Localization.Away s) z} :
        Set (Localization.Away s)) := by
    apply le_antisymm
    · simpa only [Ideal.map_span, Set.image_singleton] using hleAway
    · exact (Ideal.span_singleton_le_iff_mem
        (I.map (algebraMap A (Localization.Away s)))).mpr
          (Ideal.mem_map_of_mem _ hzI)
  have ha0 : a ≠ 0 := (isRegular_iff_ne_zero).mp haRegular
  have hz0 : z ≠ 0 := by
    intro hz
    have hprod : a * algebraMap A S (d : A) = 0 := by
      calc
        a * algebraMap A S (d : A) = algebraMap A S z := hzd
        _ = 0 := by rw [hz]; exact map_zero _
    exact (mul_ne_zero ha0 hdUnit.ne_zero) hprod
  have hs0 : s ≠ 0 := by
    intro hzero
    exact hsQ (by simpa [hzero] using Q.zero_mem)
  letI : IsDomain (Localization.Away s) := Localization.Away.isDomain hs0
  have hAwayInj : Function.Injective (algebraMap A (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hs0)
  have hzAway0 : algebraMap A (Localization.Away s) z ≠ 0 := by
    intro hzero
    exact hz0 (hAwayInj (by simpa using hzero))
  exact ⟨s, hsQ, z, hzI, isRegular_iff_ne_zero.mpr hzAway0, hAwayEq⟩

/-- At any specialization `Q` of a height-one curve prime `P`, factoriality
of the local ring at `Q` gives an actual regular principal equation on a
basic open neighborhood of `Q`. No factoriality of the global affine chart
is assumed. -/
theorem heightOnePrime_localCartier_atPrime_of_localUFD
    {A : Type u} [CommRing A] [IsDomain A]
    (P Q : Ideal A) [P.IsPrime] [Q.IsPrime]
    (hfg : P.FG) (hheight : P.height = 1) (hPQ : P ≤ Q)
    [WfDvdMonoid (Localization.AtPrime Q)]
    [UniqueFactorizationMonoid (Localization.AtPrime Q)] :
    ∃ s : A, s ∉ Q ∧ ∃ z : A, z ∈ P ∧
      IsRegular (algebraMap A (Localization.Away s) z) ∧
      P.map (algebraMap A (Localization.Away s)) =
        Ideal.span ({algebraMap A (Localization.Away s) z} :
          Set (Localization.Away s)) :=
  ideal_localRegularPrincipal_spreads_to_basicOpen P Q hfg
    (heightOnePrime_localized_regularPrincipal_of_localUFD
      P Q hPQ hheight)

/-- A principal localized curve ideal spreads to a regular equation on a
basic open around the point, without factoriality of the whole stalk. -/
theorem heightOnePrime_localCartier_atPrime_of_localPrincipal
    {A : Type u} [CommRing A] [IsDomain A]
    (P Q : Ideal A) [P.IsPrime] [Q.IsPrime]
    (hfg : P.FG) (hheight : P.height = 1) (hPQ : P ≤ Q)
    (hprincipal : (P.map (algebraMap A (Localization.AtPrime Q))).IsPrincipal) :
    ∃ s : A, s ∉ Q ∧ ∃ z : A, z ∈ P ∧
      IsRegular (algebraMap A (Localization.Away s) z) ∧
      P.map (algebraMap A (Localization.Away s)) =
        Ideal.span ({algebraMap A (Localization.Away s) z} :
          Set (Localization.Away s)) :=
  ideal_localRegularPrincipal_spreads_to_basicOpen P Q hfg
    (heightOnePrime_localized_regularPrincipal_of_localPrincipal
      P Q hPQ hheight hprincipal)

/-- Pointwise principal generation of a specific height-one curve ideal
suffices for Cartier equations; points off the curve require no input. -/
theorem heightOnePrime_locallyCartier_of_curveLocalPrincipal
    {A : Type u} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] (hfg : P.FG) (hheight : P.height = 1)
    (hprincipal : ∀ (Q : Ideal A) [Q.IsPrime], P ≤ Q →
      (P.map (algebraMap A (Localization.AtPrime Q))).IsPrincipal) :
    ∀ (Q : Ideal A) [Q.IsPrime],
      ∃ s : A, s ∉ Q ∧ ∃ z : A, z ∈ P ∧
        IsRegular (algebraMap A (Localization.Away s) z) ∧
        P.map (algebraMap A (Localization.Away s)) =
          Ideal.span ({algebraMap A (Localization.Away s) z} :
            Set (Localization.Away s)) := by
  intro Q _
  by_cases hPQ : P ≤ Q
  · exact heightOnePrime_localCartier_atPrime_of_localPrincipal
      P Q hfg hheight hPQ (hprincipal Q hPQ)
  · apply ideal_localRegularPrincipal_spreads_to_basicOpen P Q hfg
    refine ⟨1, isRegular_one, ?_⟩
    rw [IsLocalization.AtPrime.map_eq_top_of_not_le
      (S := Localization.AtPrime Q) hPQ]
    exact Ideal.span_singleton_one.symm

/-- A finitely generated height-one prime is locally cut out by one regular
equation if every local ring at a point of the ambient affine domain is a
UFD. The proof handles points off the curve by an equation that becomes a
unit, so the criterion covers the whole ambient spectrum. -/
theorem heightOnePrime_locallyCartier_of_stalkwiseUFD
    {A : Type u} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] (hfg : P.FG) (hheight : P.height = 1)
    (hwf : ∀ (Q : Ideal A) [Q.IsPrime],
      WfDvdMonoid (Localization.AtPrime Q))
    (hufd : ∀ (Q : Ideal A) [Q.IsPrime],
      UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    ∀ (Q : Ideal A) [Q.IsPrime],
      ∃ s : A, s ∉ Q ∧ ∃ z : A, z ∈ P ∧
        IsRegular (algebraMap A (Localization.Away s) z) ∧
        P.map (algebraMap A (Localization.Away s)) =
          Ideal.span ({algebraMap A (Localization.Away s) z} :
            Set (Localization.Away s)) := by
  intro Q _
  by_cases hPQ : P ≤ Q
  · letI : WfDvdMonoid (Localization.AtPrime Q) := hwf Q
    letI : UniqueFactorizationMonoid (Localization.AtPrime Q) := hufd Q
    exact heightOnePrime_localCartier_atPrime_of_localUFD
      P Q hfg hheight hPQ
  · apply ideal_localRegularPrincipal_spreads_to_basicOpen P Q hfg
    refine ⟨1, isRegular_one, ?_⟩
    rw [IsLocalization.AtPrime.map_eq_top_of_not_le
      (S := Localization.AtPrime Q) hPQ]
    exact Ideal.span_singleton_one.symm

/-- Only stalks centered on the curve need to be factorial. At a point off
the curve the localized curve ideal is the unit ideal, independent of any
factoriality assumption. -/
theorem heightOnePrime_locallyCartier_of_curveLocalUFD
    {A : Type u} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] (hfg : P.FG) (hheight : P.height = 1)
    (hwf : ∀ (Q : Ideal A) [Q.IsPrime], P ≤ Q →
      WfDvdMonoid (Localization.AtPrime Q))
    (hufd : ∀ (Q : Ideal A) [Q.IsPrime], P ≤ Q →
      UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    ∀ (Q : Ideal A) [Q.IsPrime],
      ∃ s : A, s ∉ Q ∧ ∃ z : A, z ∈ P ∧
        IsRegular (algebraMap A (Localization.Away s) z) ∧
        P.map (algebraMap A (Localization.Away s)) =
          Ideal.span ({algebraMap A (Localization.Away s) z} :
            Set (Localization.Away s)) := by
  intro Q _
  by_cases hPQ : P ≤ Q
  · letI : WfDvdMonoid (Localization.AtPrime Q) := hwf Q hPQ
    letI : UniqueFactorizationMonoid (Localization.AtPrime Q) := hufd Q hPQ
    exact heightOnePrime_localCartier_atPrime_of_localUFD
      P Q hfg hheight hPQ
  · apply ideal_localRegularPrincipal_spreads_to_basicOpen P Q hfg
    refine ⟨1, isRegular_one, ?_⟩
    rw [IsLocalization.AtPrime.map_eq_top_of_not_le
      (S := Localization.AtPrime Q) hPQ]
    exact Ideal.span_singleton_one.symm

/-- Stalkwise effective-Cartier condition on the *actual* projective quotient
chart kernels. It asks for a regular principal equation on a basic open
around each point of every standard chart, not one equation on a whole
standard chart. -/
def HasStalkwiseRegularPrincipalStandardCharts
    {R : Type u} {σ : Type} [CommRing R]
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R))
    (hIJ : I.toIdeal ≤ J.toIdeal) : Prop :=
  ∀ j : σ, ∀ (Q : Ideal (ChartRing I j)) [Q.IsPrime],
    ∃ s : ChartRing I j, s ∉ Q ∧
      ∃ z : ChartRing I j,
        z ∈ RingHom.ker (chartQuotientMap I J hIJ j) ∧
        IsRegular (algebraMap (ChartRing I j)
          (Localization.Away s) z) ∧
        (RingHom.ker (chartQuotientMap I J hIJ j)).map
          (algebraMap (ChartRing I j) (Localization.Away s)) =
          Ideal.span ({algebraMap (ChartRing I j)
            (Localization.Away s) z} : Set (Localization.Away s))

/-- Local factoriality of all chart stalks gives a stalkwise Cartier
equation for the genuine projective quotient immersion. This does not
assume any whole standard chart is factorial. -/
theorem hasStalkwiseRegularPrincipalStandardCharts_of_localUFD
    {R : Type u} {σ : Type} [CommRing R]
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (hdom : ∀ j : σ, IsDomain (ChartRing I j))
    (hfg : ∀ j : σ,
      (RingHom.ker (chartQuotientMap I J hIJ j)).FG)
    (hprime : ∀ j : σ,
      (RingHom.ker (chartQuotientMap I J hIJ j)).IsPrime)
    (hheight : ∀ j : σ,
      (RingHom.ker (chartQuotientMap I J hIJ j)).height = 1)
    (hwf : ∀ (j : σ) (Q : Ideal (ChartRing I j)) [Q.IsPrime],
      RingHom.ker (chartQuotientMap I J hIJ j) ≤ Q →
        WfDvdMonoid (Localization.AtPrime Q))
    (hufd : ∀ (j : σ) (Q : Ideal (ChartRing I j)) [Q.IsPrime],
      RingHom.ker (chartQuotientMap I J hIJ j) ≤ Q →
        UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    HasStalkwiseRegularPrincipalStandardCharts I J hIJ := by
  intro j Q _
  letI : IsDomain (ChartRing I j) := hdom j
  let P := RingHom.ker (chartQuotientMap I J hIJ j)
  letI : P.IsPrime := hprime j
  exact heightOnePrime_locallyCartier_of_curveLocalUFD
    P (hfg j) (hheight j) (hwf j) (hufd j) Q

/-- A projective curve can miss a standard chart; there the quotient kernel
is `⊤` and the local equation is the unit `1`. This version handles that
case and asks for height-one primality only on charts meeting the curve. -/
theorem hasStalkwiseRegularPrincipalStandardCharts_of_top_or_prime_localUFD
    {R : Type u} {σ : Type} [CommRing R]
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (hdom : ∀ j : σ, IsDomain (ChartRing I j))
    (hfg : ∀ j : σ,
      (RingHom.ker (chartQuotientMap I J hIJ j)).FG)
    (hkernel : ∀ j : σ,
      let P := RingHom.ker (chartQuotientMap I J hIJ j)
      P = ⊤ ∨ (P.IsPrime ∧ P.height = 1))
    (hwf : ∀ (j : σ) (Q : Ideal (ChartRing I j)) [Q.IsPrime],
      RingHom.ker (chartQuotientMap I J hIJ j) ≤ Q →
        WfDvdMonoid (Localization.AtPrime Q))
    (hufd : ∀ (j : σ) (Q : Ideal (ChartRing I j)) [Q.IsPrime],
      RingHom.ker (chartQuotientMap I J hIJ j) ≤ Q →
        UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    HasStalkwiseRegularPrincipalStandardCharts I J hIJ := by
  intro j Q _
  letI : IsDomain (ChartRing I j) := hdom j
  let P := RingHom.ker (chartQuotientMap I J hIJ j)
  rcases hkernel j with htop | ⟨hprime, hheight⟩
  · refine ⟨1, ?_, 1, ?_, ?_, ?_⟩
    · intro h1
      exact (show Q.IsPrime from inferInstance).ne_top
        ((Ideal.eq_top_iff_one Q).mpr h1)
    · simpa only [htop] using (Submodule.mem_top :
        (1 : ChartRing I j) ∈ (⊤ : Ideal (ChartRing I j)))
    · simpa using (isRegular_one : IsRegular (1 : Localization.Away (1 : ChartRing I j)))
    · rw [htop, map_one, Ideal.span_singleton_one]
      exact Ideal.map_top _
  · letI : P.IsPrime := hprime
    exact heightOnePrime_locallyCartier_of_curveLocalUFD
      P (hfg j) hheight (hwf j) (hufd j) Q

/-- For a specified projective curve, principal generation of its actual
chart kernel at points on the curve suffices for local Cartier equations. -/
theorem hasStalkwiseRegularPrincipalStandardCharts_of_top_or_prime_localPrincipal
    {R : Type u} {σ : Type} [CommRing R]
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (hdom : ∀ j : σ, IsDomain (ChartRing I j))
    (hfg : ∀ j : σ,
      (RingHom.ker (chartQuotientMap I J hIJ j)).FG)
    (hkernel : ∀ j : σ,
      let P := RingHom.ker (chartQuotientMap I J hIJ j)
      P = ⊤ ∨ (P.IsPrime ∧ P.height = 1))
    (hprincipal : ∀ (j : σ) (Q : Ideal (ChartRing I j)) [Q.IsPrime],
      RingHom.ker (chartQuotientMap I J hIJ j) ≤ Q →
        ((RingHom.ker (chartQuotientMap I J hIJ j)).map
          (algebraMap (ChartRing I j) (Localization.AtPrime Q))).IsPrincipal) :
    HasStalkwiseRegularPrincipalStandardCharts I J hIJ := by
  intro j Q _
  letI : IsDomain (ChartRing I j) := hdom j
  let P := RingHom.ker (chartQuotientMap I J hIJ j)
  rcases hkernel j with htop | ⟨hprime, hheight⟩
  · refine ⟨1, ?_, 1, ?_, ?_, ?_⟩
    · intro h1
      exact (show Q.IsPrime from inferInstance).ne_top
        ((Ideal.eq_top_iff_one Q).mpr h1)
    · simpa only [htop] using (Submodule.mem_top :
        (1 : ChartRing I j) ∈ (⊤ : Ideal (ChartRing I j)))
    · simpa using (isRegular_one : IsRegular (1 : Localization.Away (1 : ChartRing I j)))
    · rw [htop, map_one, Ideal.span_singleton_one]
      exact Ideal.map_top _
  · letI : P.IsPrime := hprime
    exact heightOnePrime_locallyCartier_of_curveLocalPrincipal
      P (hfg j) hheight (hprincipal j) Q

/-- Each local equation in the preceding criterion belongs to a chart that
is the actual Cartesian inverse-image chart of the projective immersion. -/
theorem HasStalkwiseRegularPrincipalStandardCharts.chartPullback
    {R : Type u} {σ : Type} [CommRing R]
    {I J : HomogeneousIdeal (homogeneousSubmodule σ R)}
    {hIJ : I.toIdeal ≤ J.toIdeal}
    (H : HasStalkwiseRegularPrincipalStandardCharts I J hIJ)
    (j : σ) (Q : Ideal (ChartRing I j)) [Q.IsPrime] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (chartQuotientMap I J hIJ j)))
      (chartι J j) (chartι I j) (schemeQuotientMap I J hIJ) ∧
    ∃ s : ChartRing I j, s ∉ Q ∧
      ∃ z : ChartRing I j,
        z ∈ RingHom.ker (chartQuotientMap I J hIJ j) ∧
        IsRegular (algebraMap (ChartRing I j)
          (Localization.Away s) z) ∧
        (RingHom.ker (chartQuotientMap I J hIJ j)).map
          (algebraMap (ChartRing I j) (Localization.Away s)) =
          Ideal.span ({algebraMap (ChartRing I j)
            (Localization.Away s) z} : Set (Localization.Away s)) :=
  ⟨isPullback_schemeQuotientMap_chart I J hIJ j, H j Q⟩

/-- The actual standard-chart ideal of the fixed curve inside the cubic. -/
noncomputable abbrev fixedCurveCubicChartKernel
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal) (j : Fin 4) :
    Ideal (ChartRing (equationIdeal p hp) j) :=
  RingHom.ker (chartQuotientMap (equationIdeal p hp) C
    (equationIdeal_le_homogeneousIdeal_of_mem hp hCp) j)

/-- For the actual fixed-curve immersion into a smooth cubic, local
factoriality along the curve turns height-one chart kernels into Cartier
equations on an affine-open refinement of the cubic's standard charts.
The chart kernel is allowed to be `⊤` where the curve misses a chart. -/
theorem smoothCubic_fixedCurve_stalkwiseCartier_of_curveLocalUFD
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (hfg : ∀ j : Fin 4, (fixedCurveCubicChartKernel p hp C hCp j).FG)
    (hkernel : ∀ j : Fin 4,
      let P := fixedCurveCubicChartKernel p hp C hCp j
      P = ⊤ ∨ (P.IsPrime ∧ P.height = 1))
    (hwf : ∀ (j : Fin 4)
      (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsPrime],
      fixedCurveCubicChartKernel p hp C hCp j ≤ Q →
        WfDvdMonoid (Localization.AtPrime Q))
    (hufd : ∀ (j : Fin 4)
      (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsPrime],
      fixedCurveCubicChartKernel p hp C hCp j ≤ Q →
        UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    HasStalkwiseRegularPrincipalStandardCharts
      (equationIdeal p hp) C
      (equationIdeal_le_homogeneousIdeal_of_mem hp hCp) :=
  hasStalkwiseRegularPrincipalStandardCharts_of_top_or_prime_localUFD
    (equationIdeal p hp) C
    (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)
    (smoothCubic_chartRing_isDomain p hp hp0)
    hfg hkernel hwf hufd

/-- The local Cartier equation supplied above belongs to a Cartesian chart
of the actual fixed-curve closed immersion into the cubic surface. -/
theorem fixedCurveCubic_stalkwiseCartier_chartPullback
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (H : HasStalkwiseRegularPrincipalStandardCharts
      (equationIdeal p hp) C
      (equationIdeal_le_homogeneousIdeal_of_mem hp hCp))
    (j : Fin 4)
    (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsPrime] :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (chartQuotientMap (equationIdeal p hp) C
          (equationIdeal_le_homogeneousIdeal_of_mem hp hCp) j)))
      (chartι C j) (chartι (equationIdeal p hp) j)
      (homogeneousFixedCurveToCubic p hp C hCp) ∧
    ∃ s : ChartRing (equationIdeal p hp) j, s ∉ Q ∧
      ∃ z : ChartRing (equationIdeal p hp) j,
        z ∈ fixedCurveCubicChartKernel p hp C hCp j ∧
        IsRegular (algebraMap (ChartRing (equationIdeal p hp) j)
          (Localization.Away s) z) ∧
        (fixedCurveCubicChartKernel p hp C hCp j).map
          (algebraMap (ChartRing (equationIdeal p hp) j)
            (Localization.Away s)) =
          Ideal.span ({algebraMap (ChartRing (equationIdeal p hp) j)
            (Localization.Away s) z} : Set (Localization.Away s)) :=
  H.chartPullback j Q

end PfaffianDescent

import PfaffianDescent.VoisinFixedCurveLocalUFDImmersion
import AllCharacteristics.SmoothRegularity
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.Bezout
import PfaffianDescent.VoisinCoordinateOnePDeriv
import AllCharacteristics.HypersurfaceJacobianSmooth

/-!
# Local regularity of the standard charts of a smooth cubic

Smoothness of the projective cubic restricts to each actual affine chart.
The chart coefficient algebra is therefore regular. Its prime localizations
are regular local rings, hence Noetherian; together with the domain property
of a smooth cubic chart, this supplies their well-founded divisibility.

The remaining local-factoriality hypothesis in the fixed-curve immersion
criterion is isolated below. Regular-local factoriality in dimension two is
not presently supplied by the imported algebra library.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every standard affine chart ring of a smooth cubic over a field is a
regular ring. This applies to charts without rational points as well. -/
theorem smoothCubic_chartRing_isRegularRing
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 4) :
    IsRegularRing (ChartRing (equationIdeal p hp) j) := by
  let I := equationIdeal p hp
  have hbase : Smooth (toBase I) :=
    inferInstanceAs (Smooth (hypersurfaceToBase p hp))
  letI : Smooth (toBase I) := hbase
  have hc : Smooth (chartι I j ≫ toBase I) := by infer_instance
  rw [chartι_toBase] at hc
  have hmap : (chartBaseMap I j).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mp hc
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  have hsmooth : Algebra.Smooth K (ChartRing I j) :=
    RingHom.smooth_algebraMap.mp hmap
  exact AllCharacteristics.isRegularRing_of_smooth K (ChartRing I j)

/-- The local ring at any prime of an actual smooth-cubic chart is regular. -/
theorem smoothCubic_chartLocal_isRegularLocalRing
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 4)
    (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  letI : IsRegularRing (ChartRing (equationIdeal p hp) j) :=
    smoothCubic_chartRing_isRegularRing p hp j
  infer_instance

/-- Every prime localization of a smooth cubic chart has dimension at most
two. The required Jacobian unit ideal follows from smoothness itself. -/
theorem smoothCubic_chartLocal_ringKrullDim_le_two
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4) (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) ≤ 2 := by
  apply ringKrullDim_localizationAtPrime_chartBaseMap_le_two_of_span_pderiv
    p hp j
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  let e : MvPolynomial {i : Fin 4 // i ≠ j} K →ₐ[K] ChartRing I j :=
    MvPolynomial.aeval (fun i => chartCoordinate I j i.1)
  have hthree : Ideal.span (Set.range (fun i : {k : Fin 4 // k ≠ j} =>
      e (pderiv i (coordinateOneEvaluation j p)))) = ⊤ :=
    smoothCubic_eliminatedChart_jacobian_top p hp hp0 j
  change Ideal.span (Set.range (fun i : {k : Fin 4 // k ≠ j} =>
    (pderiv i.1 p).eval₂ (chartBaseMap I j) (chartCoordinate I j))) = ⊤
  have hfun : (fun i : {k : Fin 4 // k ≠ j} =>
      (pderiv i.1 p).eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
      (fun i => e (pderiv i (coordinateOneEvaluation j p))) := by
    funext i
    exact (smoothCubic_eliminatedChart_pderiv_eq_original p hp j i).symm
  rw [hfun]
  exact hthree

/-- Every affine chart of a smooth nonzero cubic surface has Krull
dimension at most two. -/
theorem smoothCubic_chartRing_ringKrullDim_le_two
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4) :
    ringKrullDim (ChartRing (equationIdeal p hp) j) ≤ 2 := by
  rw [ringKrullDim_le_iff_height_le]
  intro Q hQ
  letI : Q.IsPrime := hQ
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)]
  exact smoothCubic_chartLocal_ringKrullDim_le_two p hp hp0 j Q

/-- A strict specialization of a height-one curve prime on a smooth cubic
chart has height exactly two. Thus the local factoriality still needed for
the curve is confined to the closed-point stalks of the surface. -/
theorem smoothCubic_chart_strictSpecialization_height_two
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4)
    (P Q : Ideal (ChartRing (equationIdeal p hp) j))
    [P.IsPrime] [Q.IsPrime] (hP : P.height = 1) (hPQ : P < Q) :
    Q.height = 2 := by
  have hlow : (2 : ℕ∞) ≤ Q.height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hPQ
    simpa [hP, one_add_one_eq_two] using h
  have hhigh : (Q.height : WithBot ℕ∞) ≤ (2 : WithBot ℕ∞) := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)]
    exact smoothCubic_chartLocal_ringKrullDim_le_two p hp hp0 j Q
  exact le_antisymm (WithBot.coe_le_coe.mp hhigh) hlow

/-- Every strict specialization of a height-one curve prime is a closed
point of the smooth cubic chart. -/
theorem smoothCubic_chart_strictSpecialization_isMaximal
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4)
    (P Q : Ideal (ChartRing (equationIdeal p hp) j))
    [P.IsPrime] [Q.IsPrime] (hP : P.height = 1) (hPQ : P < Q) :
    Q.IsMaximal := by
  have hQheight : Q.height = 2 :=
    smoothCubic_chart_strictSpecialization_height_two p hp hp0 j P Q hP hPQ
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q
    (show Q ≠ ⊤ from Ideal.IsPrime.ne_top')
  rcases lt_or_eq_of_le hQM with hlt | heq
  · letI : M.IsPrime := hM.isPrime
    have hstrict : Q.height + 1 ≤ M.height :=
      Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have hMle : M.height ≤ (2 : ℕ∞) := WithBot.coe_le_coe.mp
      ((Ideal.height_le_ringKrullDim_of_isPrime).trans
        (smoothCubic_chartRing_ringKrullDim_le_two p hp hp0 j))
    rw [hQheight] at hstrict
    have htwoThree : (2 : ℕ∞) < M.height :=
      lt_of_lt_of_le (by norm_num) hstrict
    exact False.elim ((not_lt_of_ge hMle) htwoThree)
  · exact heq ▸ hM

/-- Noetherianity and the smooth-cubic chart's domain property supply
well-founded divisibility at every prime localization. -/
theorem smoothCubic_chartLocal_wfDvdMonoid
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4) (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsPrime] :
    WfDvdMonoid (Localization.AtPrime Q) := by
  letI : IsDomain (ChartRing (equationIdeal p hp) j) :=
    smoothCubic_chartRing_isDomain p hp hp0 j
  letI : IsRegularLocalRing (Localization.AtPrime Q) :=
    smoothCubic_chartLocal_isRegularLocalRing p hp j Q
  infer_instance

/-- Every fixed-curve ideal on a standard chart of a smooth cubic is
finitely generated. The chart ring is regular and therefore Noetherian, so
this does not require a separate assumption on the curve equations. -/
theorem smoothCubic_fixedCurve_chartKernel_fg
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal) (j : Fin 4) :
    (fixedCurveCubicChartKernel p hp C hCp j).FG := by
  letI : IsRegularRing (ChartRing (equationIdeal p hp) j) :=
    smoothCubic_chartRing_isRegularRing p hp j
  exact Ideal.fg_of_isNoetherianRing _

/-- At a height-one prime of a smooth cubic chart, the regular local ring
has dimension one and is a PID, hence a UFD. This covers the generic point
of each irreducible curve component. -/
theorem smoothCubic_chart_heightOnePrime_localUFD
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4) (P : Ideal (ChartRing (equationIdeal p hp) j))
    [P.IsPrime] (hheight : P.height = 1) :
    UniqueFactorizationMonoid (Localization.AtPrime P) := by
  letI : IsDomain (ChartRing (equationIdeal p hp) j) :=
    smoothCubic_chartRing_isDomain p hp hp0 j
  letI : IsRegularLocalRing (Localization.AtPrime P) :=
    smoothCubic_chartLocal_isRegularLocalRing p hp j P
  have hdim : ringKrullDim (Localization.AtPrime P) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
    exact_mod_cast hheight
  letI : IsPrincipalIdealRing (Localization.AtPrime P) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Localization.AtPrime P)).out 4 0).mp
        (AllCharacteristics.maximalIdeal_isPrincipal_of_regularLocal_dim_one hdim)
  infer_instance

/-- A height-one fixed-curve chart kernel has a regular principal equation
on some dense basic open containing its generic point. -/
theorem smoothCubic_fixedCurve_chartKernel_denseOpen_regularPrincipal
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal) (j : Fin 4)
    (hfg : (fixedCurveCubicChartKernel p hp C hCp j).FG)
    (hprime : (fixedCurveCubicChartKernel p hp C hCp j).IsPrime)
    (hheight : (fixedCurveCubicChartKernel p hp C hCp j).height = 1) :
    let P := fixedCurveCubicChartKernel p hp C hCp j
    ∃ s : ChartRing (equationIdeal p hp) j, s ∉ P ∧
      ∃ z : ChartRing (equationIdeal p hp) j, z ∈ P ∧
        IsRegular (algebraMap (ChartRing (equationIdeal p hp) j)
          (Localization.Away s) z) ∧
        P.map (algebraMap (ChartRing (equationIdeal p hp) j)
          (Localization.Away s)) =
          Ideal.span ({algebraMap (ChartRing (equationIdeal p hp) j)
            (Localization.Away s) z} : Set (Localization.Away s)) := by
  dsimp only
  letI : IsDomain (ChartRing (equationIdeal p hp) j) :=
    smoothCubic_chartRing_isDomain p hp hp0 j
  letI : IsRegularRing (ChartRing (equationIdeal p hp) j) :=
    smoothCubic_chartRing_isRegularRing p hp j
  letI : (fixedCurveCubicChartKernel p hp C hCp j).IsPrime := hprime
  exact heightOnePrime_denseOpen_regularPrincipal_of_regularRing
    (fixedCurveCubicChartKernel p hp C hCp j) hfg hheight

/-- In the fixed-curve immersion criterion, the well-founded-divisibility
premise follows from smoothness. Only local unique factorization along the
curve is retained as an algebraic input. -/
noncomputable def smoothCubic_fixedCurve_regularPrincipalImmersion_of_curveLocalFactoriality
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (hkernel : ∀ j : Fin 4,
      let P := fixedCurveCubicChartKernel p hp C hCp j
      P = ⊤ ∨ (P.IsPrime ∧ P.height = 1))
    (hufd : ∀ (j : Fin 4)
      (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsPrime],
      fixedCurveCubicChartKernel p hp C hCp j ≤ Q →
        UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    RegularPrincipalImmersion (homogeneousFixedCurveToCubic p hp C hCp) :=
  smoothCubic_fixedCurve_regularPrincipalImmersion_of_curveLocalUFD
    p hp hp0 C hCp
    (fun j => smoothCubic_fixedCurve_chartKernel_fg p hp C hCp j) hkernel
    (fun j Q _ _ => smoothCubic_chartLocal_wfDvdMonoid p hp hp0 j Q)
    hufd

/-- In the fixed-curve criterion, factoriality at the generic point of
each nonempty height-one chart kernel is automatic. Thus it suffices to
supply factoriality only at its strict specializations. -/
noncomputable def
    smoothCubic_fixedCurve_regularPrincipalImmersion_of_strictCurveSpecializationsFactorial
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (hkernel : ∀ j : Fin 4,
      let P := fixedCurveCubicChartKernel p hp C hCp j
      P = ⊤ ∨ (P.IsPrime ∧ P.height = 1))
    (hufdStrict : ∀ (j : Fin 4)
      (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsPrime],
      fixedCurveCubicChartKernel p hp C hCp j < Q →
        UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    RegularPrincipalImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  apply smoothCubic_fixedCurve_regularPrincipalImmersion_of_curveLocalFactoriality
    p hp hp0 C hCp hkernel
  intro j Q _ hle
  let P := fixedCurveCubicChartKernel p hp C hCp j
  rcases hkernel j with htop | ⟨hprime, hheight⟩
  · have hQtop : Q = ⊤ := top_unique (htop ▸ hle)
    exact ((show Q.IsPrime from inferInstance).ne_top hQtop).elim
  · by_cases heq : P = Q
    · subst Q
      letI : P.IsPrime := hprime
      exact smoothCubic_chart_heightOnePrime_localUFD p hp hp0 j P hheight
    · exact hufdStrict j Q (lt_of_le_of_ne hle heq)

/-- The fixed-curve immersion criterion needs unique factorization only at
closed points on the curve. Smoothness and surface dimension handle every
other stalk, including the generic point of each curve component. -/
noncomputable def
    smoothCubic_fixedCurve_regularPrincipalImmersion_of_closedCurvePointsFactorial
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (hkernel : ∀ j : Fin 4,
      let P := fixedCurveCubicChartKernel p hp C hCp j
      P = ⊤ ∨ (P.IsPrime ∧ P.height = 1))
    (hufdClosed : ∀ (j : Fin 4)
      (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsMaximal],
      fixedCurveCubicChartKernel p hp C hCp j ≤ Q →
        UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    RegularPrincipalImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  apply smoothCubic_fixedCurve_regularPrincipalImmersion_of_strictCurveSpecializationsFactorial
    p hp hp0 C hCp hkernel
  intro j Q _ hPQ
  let P := fixedCurveCubicChartKernel p hp C hCp j
  rcases hkernel j with htop | ⟨hprime, hheight⟩
  · have hQtop : Q = ⊤ := top_unique (htop ▸ hPQ.le)
    exact False.elim ((show Q.IsPrime from inferInstance).ne_top hQtop)
  · letI : P.IsPrime := hprime
    letI : Q.IsMaximal :=
      smoothCubic_chart_strictSpecialization_isMaximal p hp hp0 j P Q hheight hPQ
    exact hufdClosed j Q hPQ.le

/-- A curve-specific principal equation at each closed point on the fixed
curve is enough for the Cartier immersion. At its generic point, the
height-one regular local ring supplies a principal equation automatically. -/
noncomputable def
    smoothCubic_fixedCurve_regularPrincipalImmersion_of_closedCurvePointsPrincipal
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (hkernel : ∀ j : Fin 4,
      let P := fixedCurveCubicChartKernel p hp C hCp j
      P = ⊤ ∨ (P.IsPrime ∧ P.height = 1))
    (hprincipalClosed : ∀ (j : Fin 4)
      (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsMaximal],
      fixedCurveCubicChartKernel p hp C hCp j ≤ Q →
        ((fixedCurveCubicChartKernel p hp C hCp j).map
          (algebraMap (ChartRing (equationIdeal p hp) j)
            (Localization.AtPrime Q))).IsPrincipal) :
    RegularPrincipalImmersion (homogeneousFixedCurveToCubic p hp C hCp) := by
  apply fixedCurveCubic_regularPrincipalImmersion_of_stalkwise p hp C hCp
  apply hasStalkwiseRegularPrincipalStandardCharts_of_top_or_prime_localPrincipal
    (equationIdeal p hp) C
    (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)
    (fun j => smoothCubic_chartRing_isDomain p hp hp0 j)
    (fun j => smoothCubic_fixedCurve_chartKernel_fg p hp C hCp j)
    hkernel
  intro j Q _ hPQ
  let P := fixedCurveCubicChartKernel p hp C hCp j
  rcases hkernel j with htop | ⟨hprime, hheight⟩
  · have hQtop : Q = ⊤ := top_unique (htop ▸ hPQ)
    exact False.elim ((show Q.IsPrime from inferInstance).ne_top hQtop)
  · letI : IsDomain (ChartRing (equationIdeal p hp) j) :=
      smoothCubic_chartRing_isDomain p hp hp0 j
    letI : P.IsPrime := hprime
    by_cases heq : P = Q
    · subst Q
      letI : WfDvdMonoid (Localization.AtPrime P) :=
        smoothCubic_chartLocal_wfDvdMonoid p hp hp0 j P
      letI : UniqueFactorizationMonoid (Localization.AtPrime P) :=
        smoothCubic_chart_heightOnePrime_localUFD p hp hp0 j P hheight
      obtain ⟨z, _, hz⟩ :=
        heightOnePrime_localized_regularPrincipal_of_localUFD P P
          (le_refl P) hheight
      exact ⟨z, hz⟩
    · have hlt : P < Q := lt_of_le_of_ne hPQ heq
      letI : Q.IsMaximal :=
        smoothCubic_chart_strictSpecialization_isMaximal p hp hp0 j P Q hheight hlt
      exact hprincipalClosed j Q hPQ

end PfaffianDescent

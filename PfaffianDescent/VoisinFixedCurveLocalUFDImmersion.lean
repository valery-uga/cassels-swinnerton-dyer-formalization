import PfaffianDescent.VoisinFixedCurveStalkwiseCartierCriterion
import PfaffianDescent.VoisinRegularPrincipalPrincipalOpens
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Assemble stalkwise fixed-curve equations into a Cartier immersion

The stalkwise criterion supplies one principal open around every point of
each standard chart. These opens cover by the maximal-ideal criterion, and
localization of the chart quotient maps gives the regular-principal
closed-immersion presentation of the actual projective curve.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Choose the principal open supplied by the stalkwise certificate at a
prime point of a standard projective chart. -/
private noncomputable def stalkwiseCartierOpen
    {R : Type u} {σ : Type} [CommRing R]
    {I J : HomogeneousIdeal (homogeneousSubmodule σ R)}
    {hIJ : I.toIdeal ≤ J.toIdeal}
    (H : HasStalkwiseRegularPrincipalStandardCharts I J hIJ)
    (j : σ) (q : PrimeSpectrum (ChartRing I j)) : ChartRing I j :=
  Classical.choose (H j q.asIdeal)

/-- Every prime point belongs to its selected Cartier open. -/
private theorem stalkwiseCartierOpen_not_mem
    {R : Type u} {σ : Type} [CommRing R]
    {I J : HomogeneousIdeal (homogeneousSubmodule σ R)}
    {hIJ : I.toIdeal ≤ J.toIdeal}
    (H : HasStalkwiseRegularPrincipalStandardCharts I J hIJ)
    (j : σ) (q : PrimeSpectrum (ChartRing I j)) :
    stalkwiseCartierOpen H j q ∉ q.asIdeal :=
  (Classical.choose_spec (H j q.asIdeal)).1

/-- The selected principal opens cover each standard affine chart. -/
private theorem stalkwiseCartierOpen_span_top
    {R : Type u} {σ : Type} [CommRing R]
    {I J : HomogeneousIdeal (homogeneousSubmodule σ R)}
    {hIJ : I.toIdeal ≤ J.toIdeal}
    (H : HasStalkwiseRegularPrincipalStandardCharts I J hIJ)
    (j : σ) :
    Ideal.span (Set.range (stalkwiseCartierOpen H j)) = ⊤ := by
  classical
  by_contra hnot
  obtain ⟨M, hmax, hle⟩ :=
    Ideal.exists_le_maximal
      (Ideal.span (Set.range (stalkwiseCartierOpen H j))) hnot
  let q : PrimeSpectrum (ChartRing I j) := ⟨M, hmax.isPrime⟩
  have hmem : stalkwiseCartierOpen H j q ∈ M := by
    apply hle
    exact Ideal.subset_span (Set.mem_range_self q)
  exact stalkwiseCartierOpen_not_mem H j q hmem

/-- Quasi-compactness of the affine chart turns the point-indexed family of
Cartier opens into a finite subcover, indexed in `Type` by `Fin n`. -/
private theorem exists_finiteStalkwiseCartierCover
    {R : Type u} {σ : Type} [CommRing R]
    {I J : HomogeneousIdeal (homogeneousSubmodule σ R)}
    {hIJ : I.toIdeal ≤ J.toIdeal}
    (H : HasStalkwiseRegularPrincipalStandardCharts I J hIJ)
    (j : σ) :
    ∃ n : ℕ, ∃ q : Fin n → PrimeSpectrum (ChartRing I j),
      Ideal.span (Set.range (fun i => stalkwiseCartierOpen H j (q i))) = ⊤ := by
  classical
  obtain ⟨T, hTsub, hTtop⟩ :=
    (Ideal.span_eq_top_iff_finite
      (Set.range (stalkwiseCartierOpen H j))).mp
        (stalkwiseCartierOpen_span_top H j)
  obtain ⟨n, f, hf⟩ := T.finite_toSet.fin_embedding
  have hmem (i : Fin n) : (f i : ChartRing I j) ∈
      Set.range (stalkwiseCartierOpen H j) := by
    apply hTsub
    rw [← hf]
    exact Set.mem_range_self i
  let q : Fin n → PrimeSpectrum (ChartRing I j) :=
    fun i => Classical.choose (hmem i)
  have hq (i : Fin n) : stalkwiseCartierOpen H j (q i) = f i := by
    exact Classical.choose_spec (hmem i)
  refine ⟨n, q, ?_⟩
  calc
    Ideal.span (Set.range (fun i => stalkwiseCartierOpen H j (q i))) =
        Ideal.span (Set.range (f : Fin n → ChartRing I j)) := by
          congr 1
          exact congrArg Set.range (funext hq)
    _ = Ideal.span (T : Set (ChartRing I j)) := by rw [hf]
    _ = ⊤ := hTtop

private noncomputable def finiteStalkwiseCartierCover
    {R : Type u} {σ : Type} [CommRing R]
    {I J : HomogeneousIdeal (homogeneousSubmodule σ R)}
    {hIJ : I.toIdeal ≤ J.toIdeal}
    (H : HasStalkwiseRegularPrincipalStandardCharts I J hIJ)
    (j : σ) :
    Σ n : ℕ, {q : Fin n → PrimeSpectrum (ChartRing I j) //
      Ideal.span (Set.range (fun i => stalkwiseCartierOpen H j (q i))) = ⊤} := by
  classical
  let h := exists_finiteStalkwiseCartierCover H j
  exact ⟨Classical.choose h,
    ⟨Classical.choose (Classical.choose_spec h),
      Classical.choose_spec (Classical.choose_spec h)⟩⟩

/-- Stalkwise regular-principal chart kernels assemble into a scheme-level
regular-principal immersion of the actual projective quotient. -/
noncomputable def HasStalkwiseRegularPrincipalStandardCharts.toImmersion
    {R : Type u} {σ : Type} [CommRing R]
    {I J : HomogeneousIdeal (homogeneousSubmodule σ R)}
    {hIJ : I.toIdeal ≤ J.toIdeal}
    (H : HasStalkwiseRegularPrincipalStandardCharts I J hIJ) :
    RegularPrincipalImmersion (schemeQuotientMap I J hIJ) := by
  let D (j : σ) := finiteStalkwiseCartierCover H j
  let ι (j : σ) := Fin (D j).1
  let q (j : σ) (k : ι j) : PrimeSpectrum (ChartRing I j) :=
    (D j).2.1 k
  let s : ∀ j, ι j → ChartRing I j :=
    fun j k => stalkwiseCartierOpen H j (q j k)
  have hcover : ∀ j, Ideal.span (Set.range (s j)) = ⊤ := by
    intro j
    exact (D j).2.2
  have hprincipal : ∀ (j : σ) (k : ι j),
      let q := chartQuotientMap I J hIJ j
      ∃ z : Localization.Away (s j k),
        IsRegular z ∧
          RingHom.ker (Localization.awayMap q (s j k)) =
            Ideal.span ({z} : Set (Localization.Away (s j k))) := by
    intro j k
    obtain ⟨z, _hzker, hzreg, hzideal⟩ :=
      (Classical.choose_spec (H j (q j k).asIdeal)).2
    refine ⟨algebraMap (ChartRing I j) (Localization.Away (s j k)) z,
      hzreg, ?_⟩
    have hkerLoc :
        RingHom.ker
          (Localization.awayMap (chartQuotientMap I J hIJ j) (s j k)) =
        (RingHom.ker (chartQuotientMap I J hIJ j)).map
          (algebraMap (ChartRing I j) (Localization.Away (s j k))) := by
      simpa only [Localization.awayMap, IsLocalization.Away.map] using
        (IsLocalization.ker_map
          (S := Localization.Away (s j k))
          (Q := Localization.Away
            (chartQuotientMap I J hIJ j (s j k)))
          (g := chartQuotientMap I J hIJ j)
          (Submonoid.map_powers (chartQuotientMap I J hIJ j) (s j k)))
    exact hkerLoc.trans hzideal
  exact regularPrincipalImmersion_of_principalOpenCharts
    I J hIJ ι s hcover hprincipal

/-- The stalkwise certificate gives an actual Cartier presentation of the
fixed-curve closed immersion into its cubic. -/
noncomputable def fixedCurveCubic_regularPrincipalImmersion_of_stalkwise
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (H : HasStalkwiseRegularPrincipalStandardCharts
      (equationIdeal p hp) C
      (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)) :
    RegularPrincipalImmersion (homogeneousFixedCurveToCubic p hp C hCp) :=
  H.toImmersion

/-- Local factoriality only at points of the fixed curve, together with
height-one primality of every nonempty chart kernel, gives the scheme-level
Cartier immersion into a smooth cubic. The standard chart rings themselves
are not assumed factorial. -/
noncomputable def smoothCubic_fixedCurve_regularPrincipalImmersion_of_curveLocalUFD
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
    RegularPrincipalImmersion (homogeneousFixedCurveToCubic p hp C hCp) :=
  fixedCurveCubic_regularPrincipalImmersion_of_stalkwise p hp C hCp
    (smoothCubic_fixedCurve_stalkwiseCartier_of_curveLocalUFD
      p hp hp0 C hCp hfg hkernel hwf hufd)

end PfaffianDescent

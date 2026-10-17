import PfaffianDescent.CorayHomogeneousMinimalPrimeNativeChart
import PfaffianDescent.CoraySelectedComponentHeightAndRelevance
import PfaffianDescent.CorayNormalizationClosedPointNongeneric
import PfaffianDescent.CorayPerfectOwnNormalizationStalkDimension

/-! SOURCE ONLY / UNVERIFIED. Closed points on the OWN minimal component's
actual normalization are nongeneric; actual original minimal-prime geometry
excludes zero-dimensional components. No integral whole-CI, CharZero, Infinite,
constants equality, genus, duality, Euler, point-DVR or non-singleton premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual minimal component of a literal two-equation affine-three-space
quotient cannot have a field as its own coordinate ring. The polynomial kernel
is a minimal prime over TWO equations, hence height<=2; a field quotient makes
that SAME kernel maximal of height3. No dimension certificate is supplied. -/
theorem affineThreeSpace_pairQuotient_minimalPrimeTarget_not_isField
    {K B : Type u} [Field K] [CommRing B]
    (f g : MvPolynomial (Fin 3) K)
    (rho : (MvPolynomial (Fin 3) K ⧸
      Ideal.span ({f, g} : Set (MvPolynomial (Fin 3) K))) →+* B)
    (hrho : Function.Surjective rho)
    (hmin : RingHom.ker rho ∈ minimalPrimes
      (MvPolynomial (Fin 3) K ⧸ Ideal.span ({f, g} : Set (MvPolynomial (Fin 3) K)))) :
    ¬ IsField B := by
  classical
  let J := Ideal.span ({f, g} : Set (MvPolynomial (Fin 3) K))
  let alpha := Ideal.Quotient.mk J
  let beta := rho.comp alpha
  have hminimal := Ideal.minimalPrimes_comap_of_surjective
    (Ideal.Quotient.mk_surjective (I := J)) hmin
  have hbetaMin : RingHom.ker beta ∈ J.minimalPrimes := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker, RingHom.comap_ker] at hminimal
    exact hminimal
  intro hfield
  letI : Field B := hfield.toField
  letI : (RingHom.ker beta).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective beta
      (hrho.comp (Ideal.Quotient.mk_surjective (I := J)))
  have hheight : (RingHom.ker beta).height = 3 := by
    simpa using maximalIdeal_height_mvPolynomial (RingHom.ker beta)
  have hminimal' : RingHom.ker beta ∈ (Ideal.span
      (({f, g} : Finset (MvPolynomial (Fin 3) K)) : Set _)).minimalPrimes := by
    simpa only [J, Finset.coe_insert, Finset.coe_singleton] using hbetaMin
  have hle := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hminimal'
  have hcard : ({f, g} : Finset (MvPolynomial (Fin 3) K)).card ≤ 2 :=
    (Finset.card_insert_le f {g}).trans (by simp)
  have hleTwo : (RingHom.ker beta).height ≤ 2 := hle.trans (by exact_mod_cast hcard)
  rw [hheight] at hleTwo
  norm_num at hleTwo

/-- Genuine OWN minimal-component non-singleton geometry. The SAME nonempty
coordinate chart would be a field if C had only one projective point, while
its actual native chart kernel is minimal over the original two equations.
Neither irrelevance, chart minimality nor a non-singleton proof is an input. -/
theorem selectedProjectiveMinimalComponent_not_subsingleton
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) : ¬ Subsingleton (scheme C) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme C
  letI : IsIntegral X := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  intro hsingle
  letI : Subsingleton X := hsingle
  obtain ⟨j, z, _hz⟩ := exists_coordinate_chart C P
  let A := Spec (.of (ChartRing C j))
  letI : Nonempty A := ⟨z⟩
  letI : IsIntegral A := isIntegral_of_isOpenImmersion (chartι C j)
  letI : Subsingleton A := ⟨fun s t =>
    (chartι C j).isOpenEmbedding.injective (Subsingleton.elim _ _)⟩
  have hsections : IsField Γ(A, ⊤) := isField_of_isIntegral_of_subsingleton A
  have hchart : IsField (ChartRing C j) :=
    MulEquiv.isField hsections
      (Scheme.ΓSpecIso (.of (ChartRing C j))).symm.commRingCatIsoToRingEquiv.toMulEquiv
  letI : Field (ChartRing C j) := hchart.toField
  let f := chartQuotientMap I C hmin.le j
  have hkerne : RingHom.ker f ≠ ⊤ := (RingHom.ker_isPrime f).ne_top
  rcases homogeneousMinimalPrime_nativeChartKernel_top_or_minimalPrime I C hmin
      (selectedProjectiveMinimalComponent_homogeneous_relevant
        p q hp hp0 n hq hnot C hmin) j with htop | ⟨_hprime, hminimal⟩
  · exact hkerne htop
  · let E := projectiveIntersection_chartRingEquiv p q hp hq j
    let rho := f.comp E.symm.toRingHom
    have hrho : Function.Surjective rho :=
      (chartQuotientMap_surjective I C hmin.le j).comp E.symm.surjective
    have hminimal' := Ideal.minimalPrimes_comap_of_surjective
      (f := E.symm.toRingHom) E.symm.surjective hminimal
    have hbot : (⊥ : Ideal (ChartRing I j)).comap E.symm.toRingHom = ⊥ := by
      ext a
      change E.symm a = 0 ↔ a = 0
      exact map_eq_zero_iff E.symm E.symm.injective
    rw [hbot, RingHom.comap_ker] at hminimal'
    exact affineThreeSpace_pairQuotient_minimalPrimeTarget_not_isField
      (normalizedAffineEquation j p) (normalizedAffineEquation j q) rho hrho hminimal' hchart

/-- Every closed point on the SAME own minimal component's normalization is
nongeneric. Actual normalization surjectivity and the preceding internally
constructed non-singleton geometry exclude a closed generic point. -/
theorem selectedProjectiveMinimalComponent_genericNormalization_closedPoint_ne_generic
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ Q : closedPoints N, Q.1 ≠ genericPoint N := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  change ∀ Q : closedPoints N, Q.1 ≠ genericPoint N
  intro Q hQ
  have hclosed : IsClosed ({genericPoint N} : Set N) := by
    simpa only [hQ] using (mem_closedPoints_iff.mp Q.2 : IsClosed ({Q.1} : Set N))
  have hall : (Set.univ : Set N) = {genericPoint N} :=
    (genericPoint_spec N).symm.trans hclosed.closure_eq
  letI : Subsingleton N := ⟨fun s t => by
    have hs : s = genericPoint N := Set.mem_singleton_iff.mp (hall ▸ Set.mem_univ s)
    have ht : t = genericPoint N := Set.mem_singleton_iff.mp (hall ▸ Set.mem_univ t)
    exact hs.trans ht.symm⟩
  have hsurj : Function.Surjective nu :=
    (integralGenericNormalization_fromNormalization_surjective X).surj
  letI : Subsingleton X := ⟨fun s t => by
    obtain ⟨s', rfl⟩ := hsurj s
    obtain ⟨t', rfl⟩ := hsurj t
    exact congrArg nu (Subsingleton.elim s' t')⟩
  exact selectedProjectiveMinimalComponent_not_subsingleton p q hp hp0 n hq hnot C hmin P
    inferInstance

/-- All ACTUAL closed points on the OWN minimal component's SAME normalization
have native DVR stalks over original perfect K. Minimality, actual native charts,
normalization surjectivity, finite normalization and native normality derive all
local geometry internally; no nongenericity, DVR or field-constants premise. -/
theorem perfectField_selectedProjectiveMinimalComponent_genericNormalization_closedPoint_stalk_isDVR
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ Q : closedPoints N, IsDiscreteValuationRing (N.presheaf.stalk Q.1) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  change ∀ Q : closedPoints N, IsDiscreteValuationRing (N.presheaf.stalk Q.1)
  intro Q
  exact perfectField_selectedProjectivePrimeComponent_genericNormalization_nongeneric_stalk_isDVR
    p q hp hp0 n hq hnot C hmin.le hmin.isPrime P Q.1
    (selectedProjectiveMinimalComponent_genericNormalization_closedPoint_ne_generic
      p q hp hp0 n hq hnot C hmin P Q)

end PfaffianDescent.Coray

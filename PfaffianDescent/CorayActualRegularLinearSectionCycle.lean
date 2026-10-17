import PfaffianDescent.CorayCubicDegreeNLinearSectionCycle
import PfaffianDescent.CorayActualNormalizationSupportLinearSectionChoice
import PfaffianDescent.CorayOutsideActualNormalizationSupportRegular

/-! Construct the actual degree-3*n linear-section cycle on the OWN original
selected curve, supported on its OWN regular locus. Literal regular-sequence
selection, length, finite scheme and support regularity are proved internally.
Pending native quotient-stalk comparison remains an explicit import dependency.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The OWN defining H vanishes at every point in the actual section's image.
This is reduction of the actual Proj map to its contracted prime, then literal
quotient membership; image equality is not supplied. -/
theorem cubic_degree_n_linear_section_curveImmersion_equation_mem
    (p q H : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1)
    (x : scheme (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH)) :
    Ideal.Quotient.mk (projectiveIntersectionIdeal p q hp hq).toIdeal H ∈
      (cubic_degree_n_linear_section_curveImmersion p q H hp hq hH x).asHomogeneousIdeal := by
  let I := projectiveIntersectionIdeal p q hp hq
  let J := tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH
  let hIJ := cubic_degree_n_linear_section_curveIdeal_le p q H hp hq hH
  change gradedQuotientMap I J hIJ (Ideal.Quotient.mk I.toIdeal H) ∈ x.asHomogeneousIdeal
  change Ideal.Quotient.mk J.toIdeal H ∈ x.asHomogeneousIdeal
  have hHmem : H ∈ J.toIdeal := by
    change H ∈ Ideal.span ({p, q, H} : Set (MvPolynomial (Fin 4) K))
    apply Ideal.subset_span
    simp
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hHmem]
  exact x.asHomogeneousIdeal.toIdeal.zero_mem

/-- ACTUAL third-equation choice and ACTUAL regular-supported degree3*n
curve cycle, including all native nonreduced multiplicities and FULL original
K residue degrees. No equation, cycle, degree or regularity certificate is input. -/
theorem projectiveIntersection_exists_regular_linearSection_cycle_degree_three_mul
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    ∃ H : MvPolynomial (Fin 4) K, ∃ hH : H.IsHomogeneous 1,
      (∀ x : MvPolynomial (Fin 4) K,
        H * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
      ∃ z : EffectiveZeroCycle (scheme (projectiveIntersectionIdeal p q hp hq)),
        EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) z = 3 * n ∧
        (∀ P ∈ z.support, IsRegularLocalRing
          ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1)) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  obtain ⟨H, hH, hregular, havoid⟩ :=
    projectiveIntersection_exists_regular_linear_avoiding_actualNormalizationQuotientSupport
      p q hp hp0 n hq hnot
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hnot
    rw [hzero]
    exact Ideal.zero_mem _
  have hrel := isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot
  let J := tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH
  let i := cubic_degree_n_linear_section_curveImmersion p q H hp hq hH
  letI : IsClosedImmersion i :=
    cubic_degree_n_linear_section_curveImmersion_isClosedImmersion p q H hp hq hH
  letI : IsFinite (toBase J) :=
    cubic_degree_n_linear_section_finite p q H hp hq hH hp0 hq0 hrel hregular
  obtain ⟨zJ, hdegree⟩ := exists_effectiveZeroCycle_degree_finiteSchemeRank (toBase J)
  let z := pushforwardClosedCycle i zJ
  refine ⟨H, hH, hregular, z, ?_, ?_⟩
  · change EffectiveZeroCycle.degree (toBase I) (pushforwardClosedCycle i zJ) = 3 * n
    rw [degree_pushforwardClosedCycle]
    have hbase : i ≫ toBase I = toBase J :=
      cubic_degree_n_linear_section_curveImmersion_toBase p q H hp hq hH
    rw [hbase, hdegree]
    exact cubic_degree_n_linear_section_length_three_mul p q H hp hq hH hp0 hq0 hrel hregular
  · intro P hP
    have himage : P ∈ zJ.support.image (closedPointMap i) :=
      Finsupp.mapDomain_support hP
    obtain ⟨R, hR, hRP⟩ := Finset.mem_image.mp himage
    apply projectiveIntersection_original_stalk_regular_of_outside_actualNormalizationQuotientSupport
      p q hp hp0 n hq hnot P.1
    intro hsupport
    have hnotmem := havoid P.1 hsupport
    apply hnotmem
    have hmem := cubic_degree_n_linear_section_curveImmersion_equation_mem p q H hp hq hH R.1
    have hpoints : i R.1 = P.1 := congrArg Subtype.val hRP
    rw [hpoints] at hmem
    exact hmem

end PfaffianDescent.Coray

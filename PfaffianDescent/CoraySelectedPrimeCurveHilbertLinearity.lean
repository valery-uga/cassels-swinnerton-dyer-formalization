import PfaffianDescent.CorayLinearGradeExactSequence
import PfaffianDescent.CorayRegularPairLinearSectionAvoidance
import PfaffianDescent.CorayCubicDegreeNLinearSectionLength
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Original cubic/q minimal component: derived actual affine Hilbert function

Construct the actual regular hyperplane equation H. Derive H not in the actual
minimal prime from genuine minimal-prime zero-divisor geometry. Bound the SAME
component cut by the actual cubic/q/H Koszul Hilbert function, hence derive its
native finiteness. The actual section rank is the derived curve Hilbert slope
and is at most 3*n. No finite hyperplane, eventual polynomial, slope, degree,
or genus certificate is an input.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A literal regular equation cannot belong to an actual minimal prime over I.
This uses an actual annihilating multiplier supplied by minimal-prime theory. -/
theorem homogeneousMinimalPrime_not_mem_of_regular
    (I C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ I.toIdeal.minimalPrimes)
    (H : MvPolynomial (Fin 4) K)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      H * x ∈ I.toIdeal → x ∈ I.toIdeal) : H ∉ C.toIdeal := by
  intro hmem
  obtain ⟨x, hx, hHx⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hmin hmem
  exact hx (hregular x hHx)

/-- The actual component hyperplane quotient has its Hilbert bound from the
original triple complete intersection. No section-finiteness premise. -/
theorem selectedProjectiveComponent_regular_linearSection_hilbertBound
    (p q H : MvPolynomial (Fin 4) K) {n : ℕ}
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      H * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (m : ℕ) (hm : n + 4 ≤ m) :
    finrank K (grading (C ⊔ equationIdeal H hH) m) ≤ 3 * n := by
  let J := tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH
  let S := C ⊔ equationIdeal H hH
  have hspan : Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal := by
    simpa only [projectiveIntersectionIdeal_toIdeal] using hIC
  have hJS : J.toIdeal ≤ S.toIdeal := by
    change Ideal.span ({p, q, H} : Set (MvPolynomial (Fin 4) K)) ≤ S.toIdeal
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hpS : p ∈ S.toIdeal :=
      (le_sup_left : C.toIdeal ≤ S.toIdeal)
        (hspan (Ideal.subset_span (Set.mem_insert p {q})))
    have hqS : q ∈ S.toIdeal :=
      (le_sup_left : C.toIdeal ≤ S.toIdeal)
        (hspan (Ideal.subset_span (Set.mem_insert_of_mem p (Set.mem_singleton q))))
    have hHS : H ∈ S.toIdeal :=
      (le_sup_right : (equationIdeal H hH).toIdeal ≤ S.toIdeal)
        (Ideal.subset_span (Set.mem_singleton H))
    rcases hx with hxp | hxq | hxH
    · exact hxp.symm ▸ hpS
    · exact hxq.symm ▸ hqS
    · exact hxH.symm ▸ hHS
  have hle := homogeneousCoordinateQuotientGrade_finrank_le J S hJS m
  change finrank K (grading S m) ≤
    finrank K (tripleCompleteIntersectionComponent p q H m) at hle
  have hdim := cubic_degree_n_linear_section_hilbert_three_mul
    p q H hp hq hH hp0 hq0 hrel hregular (m - (n + 4))
  have hindex : m - (n + 4) + n + 4 = m := by omega
  rw [hindex] at hdim
  rw [hdim] at hle
  exact hle

/-- The SAME actual component cut is finite, derived from its actual bound. -/
theorem selectedProjectiveComponent_regular_linearSection_isFinite
    (p q H : MvPolynomial (Fin 4) K) {n : ℕ}
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      H * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal) :
    IsFinite (toBase (C ⊔ equationIdeal H hH)) :=
  PfaffianDescent.projective_finite_of_hilbert_bound
    (C ⊔ equationIdeal H hH) (n + 4) (3 * n)
    (selectedProjectiveComponent_regular_linearSection_hilbertBound
      p q H hp hq hH hp0 hq0 hrel hregular C hIC)

/-- An ACTUAL minimal component of the ORIGINAL smooth cubic/q admits a derived
actual affine Hilbert function. Its constructed literal section has native
scheme rank as slope, bounded by 3*n. No desired construction is supplied. -/
theorem selectedProjectiveMinimalComponent_exists_affineHilbertFunction
    [Infinite K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1),
      H ∉ C.toIdeal ∧ ∃ hfinite : IsFinite (toBase (C ⊔ equationIdeal H hH)),
        letI := hfinite
        ∃ N : ℕ, (∀ t : ℕ,
          finrank K (grading C (N + t)) = finrank K (grading C N) +
            t * finiteSchemeRank (toBase (C ⊔ equationIdeal H hH))) ∧
          finiteSchemeRank (toBase (C ⊔ equationIdeal H hH)) ≤ 3 * n := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hnot
    rw [hzero]
    exact Ideal.zero_mem _
  have hrel := isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot
  let point : PEmpty.{1} → scheme I := fun x => PEmpty.elim x
  obtain ⟨H, hH, hregular, _⟩ :=
    regular_pair_exists_linear_nonzerodivisor_avoiding_finite_projective_family
      p q hp hq hp0 hrel point
  have hregularI : ∀ x : MvPolynomial (Fin 4) K,
      H * x ∈ I.toIdeal → x ∈ I.toIdeal := by
    simpa only [I, projectiveIntersectionIdeal_toIdeal] using hregular
  have hnotC := homogeneousMinimalPrime_not_mem_of_regular I C hCmin H hregularI
  have hfinite := selectedProjectiveComponent_regular_linearSection_isFinite
    p q H hp hq hH hp0 hq0 hrel hregular C hCmin.le
  letI := hfinite
  obtain ⟨N, hN⟩ := primeComponent_hilbertFunction_affine_of_finite_linearSection C H hH hnotC
  obtain ⟨M, hM⟩ := finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank
    (C ⊔ equationIdeal H hH)
  have hbound := selectedProjectiveComponent_regular_linearSection_hilbertBound
    p q H hp hq hH hp0 hq0 hrel hregular C hCmin.le (max M (n + 4))
      (le_max_right _ _)
  rw [hM (max M (n + 4)) (le_max_left _ _)] at hbound
  exact ⟨H, hH, hnotC, hfinite, N, hN, hbound⟩

end PfaffianDescent.Coray

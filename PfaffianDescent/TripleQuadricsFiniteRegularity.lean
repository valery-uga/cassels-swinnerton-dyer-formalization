import PfaffianDescent.TripleQuadricsFiniteCodimension
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import AllCharacteristics.ProjectiveBaseChange
import Mathlib.FieldTheory.IsAlgClosed.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
/-!
# Regularity of finite nets of three quadrics

The first regularity condition in the finite-net argument follows directly
from projective finiteness.  A common factor of the first two quadrics and the
third quadric has a projective common zero; its normalized minimal prime has
height at most two, while every prime on a finite three-quadric chart has
height three.
-/

namespace PfaffianDescent
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, a finite nonempty net of three quadrics
has relatively prime first two equations.  A nonunit common factor together
with the third equation would have a projective common zero and hence give a
height-at-most-two affine prime containing the net, contradicting finiteness. -/
theorem tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty_algClosed
    (p q r : MvPolynomial (Fin 4) K) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (hc : 0 < c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hX : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    IsRelPrime p q := by
  have hlin := tripleCompleteIntersection_linearIndependent_of_finite_of_nonempty
    p q r hp hq hr hX
  have hp0 : p ≠ 0 := fun h => by
    apply hlin.ne_zero 0
    simp [h]
  by_contra hrel
  simp only [IsRelPrime] at hrel
  push Not at hrel
  obtain ⟨d, hdp, hdq, hdunit⟩ := hrel
  obtain ⟨a, hpa⟩ := hdp
  obtain ⟨b, hqb⟩ := hdq
  have hd0 : d ≠ 0 := by
    intro hd0
    apply hp0
    rw [hpa, hd0, zero_mul]
  have ha : a.IsHomogeneous a.totalDegree :=
    (homogeneous_factor_of_homogeneous_product hd0 (by
      intro ha0
      apply hp0
      rw [hpa, ha0, mul_zero]) (hpa.symm ▸ hp)).2
  have hd : d.IsHomogeneous d.totalDegree :=
    (homogeneous_factor_of_homogeneous_product hd0 (by
      intro ha0
      apply hp0
      rw [hpa, ha0, mul_zero]) (hpa.symm ▸ hp)).1
  have hdpos : 0 < d.totalDegree := by
    by_contra hnot
    apply hdunit
    apply isUnit_of_homogeneous_zero
    · rw [← Nat.eq_zero_of_not_pos hnot]
      exact hd
    · exact hd0
  obtain ⟨x, hx, hdx, hrx⟩ :=
    exists_nonzero_common_zero_of_homogeneous_pos d r hd hr hdpos hc
  have hdx' : d.eval₂ (RingHom.id K) x = 0 := by
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, RingHom.id_apply] using hdx
  have hrx' : r.eval₂ (RingHom.id K) x = 0 := by
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, RingHom.id_apply] using hrx
  obtain ⟨j, M, hMprime, hdM0, hrM0, hdM, hrM⟩ :=
    exists_normalized_common_prime_of_eval₂ d r hd hr hd0 (by
      intro hr0
      have := hlin.ne_zero 2
      simp [hr0] at this) x hx hdx' hrx'
  let e := coordinateOneQuotientEquiv (R := K) j
  let M' : Ideal (MvPolynomial {i : Fin 4 // i ≠ j} K) := M.map e.toRingHom
  have hM'prime : M'.IsPrime := by
    dsimp [M']
    exact Ideal.map_isPrime_of_equiv e.toRingEquiv
  letI : M'.IsPrime := hM'prime
  have hdM' : coordinateOneEvaluation j d ∈ M' := by
    change e (Ideal.Quotient.mk (coordinateOneIdeal j) d) ∈ M'
    rw [coordinateOneQuotientEquiv_mk]
    exact Ideal.mem_map_of_mem e.toRingHom hdM
  have hrM' : coordinateOneEvaluation j r ∈ M' := by
    change e (Ideal.Quotient.mk (coordinateOneIdeal j) r) ∈ M'
    rw [coordinateOneQuotientEquiv_mk]
    exact Ideal.mem_map_of_mem e.toRingHom hrM
  let J : Ideal (MvPolynomial {i : Fin 4 // i ≠ j} K) :=
    Ideal.span {coordinateOneEvaluation j d, coordinateOneEvaluation j r}
  have hJM' : J ≤ M' := by
    apply Ideal.span_le.mpr
    rintro z (rfl | rfl)
    · exact hdM'
    · exact hrM'
  obtain ⟨P, hPmin, hPM'⟩ := Ideal.exists_minimalPrimes_le hJM'
  have hPprime : P.IsPrime := hPmin.isPrime
  letI : P.IsPrime := hPprime
  have hPheightle : P.height ≤ 2 := by
    calc
      P.height ≤ ↑({coordinateOneEvaluation j d, coordinateOneEvaluation j r} :
          Set (MvPolynomial {i : Fin 4 // i ≠ j} K)).ncard :=
        Ideal.height_le_card_of_mem_minimalPrimes_span
          (p := P) (s := {coordinateOneEvaluation j d, coordinateOneEvaluation j r})
          (Set.toFinite _) hPmin
      _ ≤ ↑(1 + 1) := by
        exact_mod_cast (by
          simpa only [Set.ncard_singleton] using
            Set.ncard_insert_le (coordinateOneEvaluation j d)
              ({coordinateOneEvaluation j r} : Set (MvPolynomial {i : Fin 4 // i ≠ j} K)))
      _ = 2 := by norm_num
  have hdP : coordinateOneEvaluation j d ∈ P := hPmin.1.2 (Ideal.subset_span (by simp))
  have hrP : coordinateOneEvaluation j r ∈ P := hPmin.1.2 (Ideal.subset_span (by simp))
  have hpP : coordinateOneEvaluation j p ∈ P := by
    rw [hpa, map_mul]
    exact P.mul_mem_right _ hdP
  have hqP : coordinateOneEvaluation j q ∈ P := by
    rw [hqb, map_mul]
    exact P.mul_mem_right _ hdP
  have htripleP : tripleCompleteIntersectionDehomogenizedIdeal p q r j ≤ P := by
    apply Ideal.span_le.mpr
    rintro z (rfl | rfl | rfl)
    · exact hpP
    · exact hqP
    · exact hrP
  have hPheight := tripleCompleteIntersection_dehomogenized_prime_height_of_finite
    p q r hp hq hr j P htripleP
  rw [hPheight] at hPheightle
  norm_num at hPheightle


/-- Coefficient extension carries the homogeneous ideal of a three-quadric
intersection to the ideal of the coefficient-extended equations. -/
theorem tripleCompleteIntersection_map_coefficientExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (p q r : MvPolynomial (Fin 4) k) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c) :
    (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal.map
      (MvPolynomial.map (algebraMap k K)) =
    (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap k K)) (q.map (algebraMap k K)) (r.map (algebraMap k K))
      (hp.map (algebraMap k K)) (hq.map (algebraMap k K))
      (hr.map (algebraMap k K))).toIdeal := by
  rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionIdeal, Ideal.map_span,
    tripleCompleteIntersectionIdeal]
  apply congrArg Ideal.span
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with rfl | rfl | rfl <;> simp
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨p, Or.inl rfl, hx.symm⟩
    · exact ⟨q, Or.inr (Or.inl rfl), hx.symm⟩
    · exact ⟨r, Or.inr (Or.inr rfl), hx.symm⟩

/-- A finite projective three-quadric intersection stays finite after a field
coefficient extension. -/
theorem tripleCompleteIntersection_isFinite_coefficientExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (p q r : MvPolynomial (Fin 4) k) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap k K)) (q.map (algebraMap k K)) (r.map (algebraMap k K))
      (hp.map (algebraMap k K)) (hq.map (algebraMap k K))
      (hr.map (algebraMap k K)))) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let J := tripleCompleteIntersectionHomogeneousIdeal
    (p.map (algebraMap k K)) (q.map (algebraMap k K)) (r.map (algebraMap k K))
    (hp.map (algebraMap k K)) (hq.map (algebraMap k K))
    (hr.map (algebraMap k K))
  have hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal :=
    tripleCompleteIntersection_map_coefficientExtension p q r hp hq hr
  letI : IsFinite (pullback.snd (toBase I)
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  rw [← projectiveBaseChangeIso_hom_snd (algebraMap k K) I J hIJ]
  exact inferInstance

/-- A finite nonempty net of three quadrics has relatively prime first two
equations over every field.  The algebraically closed case is descended along
the faithfully flat coefficient map to the algebraic closure. -/
theorem tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty
    {k : Type u} [Field k]
    (p q r : MvPolynomial (Fin 4) k) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (hc : 0 < c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hX : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    IsRelPrime p q := by
  let K := AlgebraicClosure k
  let f : k →+* K := algebraMap k K
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let J := tripleCompleteIntersectionHomogeneousIdeal
    (p.map f) (q.map f) (r.map f) (hp.map f) (hq.map f) (hr.map f)
  have hIJ : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal :=
    tripleCompleteIntersection_map_coefficientExtension p q r hp hq hr
  have hfinite : IsFinite (toBase J) := tripleCompleteIntersection_isFinite_coefficientExtension (K := K) p q r hp hq hr
  letI : IsFinite (toBase J) := hfinite
  have hJnonempty : Nonempty (scheme J) := by
    letI : Nonempty (scheme I) := hX
    let X : Scheme := Limits.pullback (toBase I)
      (Spec.map (CommRingCat.ofHom f))
    letI : Nonempty X := inferInstance
    exact Nonempty.map (projectiveBaseChangeIso f I J hIJ).inv inferInstance
  have hrel : IsRelPrime (p.map f) (q.map f) :=
    tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty_algClosed
      (p.map f) (q.map f) (r.map f) (hp.map f) (hq.map f) (hr.map f) hc hJnonempty
  letI : IsLocalHom (MvPolynomial.map f) := {
    map_nonunit := by
      intro z hz
      apply isUnit_of_homogeneous_zero
      · apply MvPolynomial.IsHomogeneous.of_map f.injective
        exact ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 4)).mp
          (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hz).2)
      · intro hz0
        exact hz.ne_zero (by simp [hz0]) }
  exact IsRelPrime.of_map (MvPolynomial.map f) hrel

/-- Reordering the equations does not change their homogeneous complete-
intersection ideal. -/
private theorem tripleCompleteIntersectionHomogeneousIdeal_swap_second_third
    {k : Type u} [Field k]
    (p q r : MvPolynomial (Fin 4) k) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c) :
    tripleCompleteIntersectionHomogeneousIdeal p r q hp hr hq =
      tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr := by
  apply HomogeneousIdeal.ext
  rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionIdeal, tripleCompleteIntersectionIdeal]
  apply congrArg Ideal.span
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Moving the first equation to the end does not change the homogeneous
complete-intersection ideal. -/
private theorem tripleCompleteIntersectionHomogeneousIdeal_cycle
    {k : Type u} [Field k]
    (p q r : MvPolynomial (Fin 4) k) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c) :
    tripleCompleteIntersectionHomogeneousIdeal q r p hq hr hp =
      tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr := by
  apply HomogeneousIdeal.ext
  rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionIdeal, tripleCompleteIntersectionIdeal]
  apply congrArg Ideal.span
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Every pair in a finite nonempty net of three quadrics is relatively
prime.  This records the pairwise part of the complete-intersection argument
for all orderings of the net. -/
theorem tripleCompleteIntersection_pairwise_isRelPrime_of_finite_of_nonempty
    {k : Type u} [Field k]
    (p q r : MvPolynomial (Fin 4) k) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hX : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    IsRelPrime p q ∧ IsRelPrime p r ∧ IsRelPrime q r := by
  have hpq := tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty
    p q r hp hq hr hc hX
  have hprq := tripleCompleteIntersectionHomogeneousIdeal_swap_second_third
    p q r hp hq hr
  have hprfinite : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p r q hp hr hq)) := by
    rw [hprq]
    infer_instance
  letI : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p r q hp hr hq)) := hprfinite
  have hprX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal p r q hp hr hq)) := by
    rw [hprq]
    exact hX
  have hpr := tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty
    p r q hp hr hq hb hprX
  have hqrp := tripleCompleteIntersectionHomogeneousIdeal_cycle p q r hp hq hr
  have hqrfinite : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal q r p hq hr hp)) := by
    rw [hqrp]
    infer_instance
  letI : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal q r p hq hr hp)) := hqrfinite
  have hqrX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal q r p hq hr hp)) := by
    rw [hqrp]
    exact hX
  have hqr := tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty
    q r p hq hr hp ha hqrX
  exact ⟨hpq, hpr, hqr⟩

end PfaffianDescent

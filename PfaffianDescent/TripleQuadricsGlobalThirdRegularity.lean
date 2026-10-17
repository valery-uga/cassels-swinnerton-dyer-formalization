import PfaffianDescent.TripleQuadricsChartThirdRegular
import PfaffianDescent.TripleQuadricsFiniteRegularity
import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import PfaffianDescent.TwoQuadricsNoIrrelevantSocle
import PfaffianDescent.ProjectiveIdealSaturation

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma standard_chart_power_mul_mem_of_third_relation
    (p q r F : MvPolynomial (Fin 4) K) {a b c m : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (ha : 0 < a) (hF : F.IsHomogeneous m) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hglobal : r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    ∃ N : ℕ, (X (0 : Fin 4) : MvPolynomial (Fin 4) K) ^ N * F ∈
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hglobal
  have hchartrel : coordinateOneEvaluation 0 r * coordinateOneEvaluation 0 F ∈ Ideal.span
      ({coordinateOneEvaluation 0 p, coordinateOneEvaluation 0 q} :
        Set (MvPolynomial {i : Fin 4 // i ≠ 0} K)) := by
    apply Ideal.mem_span_pair.mpr
    refine ⟨coordinateOneEvaluation 0 u, coordinateOneEvaluation 0 v, ?_⟩
    simpa only [map_add, map_mul] using congrArg (coordinateOneEvaluation 0) huv
  have hchartF := tripleCompleteIntersection_coordinateOne_third_regular_of_finite_algClosed
    p q r hp hq hr ha hp0 hrel 0 (coordinateOneEvaluation 0 F) hchartrel
  have hdehomF : QuarticNet.dehomogenizeAtZero F ∈ Ideal.span
      ({QuarticNet.dehomogenizeAtZero p, QuarticNet.dehomogenizeAtZero q} :
        Set (MvPolynomial (Fin 3) K)) := by
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hchartF
    apply Ideal.mem_span_pair.mpr
    refine ⟨(MvPolynomial.renameEquiv K QuarticNet.finThreeSuccComplement.symm) u,
      (MvPolynomial.renameEquiv K QuarticNet.finThreeSuccComplement.symm) v, ?_⟩
    rw [QuarticNet.dehomogenizeAtZero_eq_rename_coordinateOneEvaluation,
      QuarticNet.dehomogenizeAtZero_eq_rename_coordinateOneEvaluation,
      QuarticNet.dehomogenizeAtZero_eq_rename_coordinateOneEvaluation]
    simpa only [map_add, map_mul] using
      congrArg (MvPolynomial.renameEquiv K QuarticNet.finThreeSuccComplement.symm) huv
  obtain ⟨N, hN⟩ := QuarticNet.power_mul_mem_span_of_dehomogenizeAtZero_mem_span hp hq hF hdehomF
  exact ⟨N, hN⟩

lemma standard_chart_localization_zero_of_third_relation
    (p q r F : MvPolynomial (Fin 4) K) {a b c m : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (ha : 0 < a) (hF : F.IsHomogeneous m) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hglobal : r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    algebraMap (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _))
      (Localization (Submonoid.powers (Ideal.Quotient.mk (Ideal.span ({p, q} :
        Set (MvPolynomial (Fin 4) K))) (X 0))))
      (Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) F) = 0 := by
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hglobal
  have hchartrel : coordinateOneEvaluation 0 r * coordinateOneEvaluation 0 F ∈ Ideal.span
      ({coordinateOneEvaluation 0 p, coordinateOneEvaluation 0 q} :
        Set (MvPolynomial {i : Fin 4 // i ≠ 0} K)) := by
    apply Ideal.mem_span_pair.mpr
    refine ⟨coordinateOneEvaluation 0 u, coordinateOneEvaluation 0 v, ?_⟩
    simpa only [map_add, map_mul] using congrArg (coordinateOneEvaluation 0) huv
  have hchartF := tripleCompleteIntersection_coordinateOne_third_regular_of_finite_algClosed
    p q r hp hq hr ha hp0 hrel 0 (coordinateOneEvaluation 0 F) hchartrel
  have hdehomF : QuarticNet.dehomogenizeAtZero F ∈ Ideal.span
      ({QuarticNet.dehomogenizeAtZero p, QuarticNet.dehomogenizeAtZero q} :
        Set (MvPolynomial (Fin 3) K)) := by
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hchartF
    apply Ideal.mem_span_pair.mpr
    refine ⟨(MvPolynomial.renameEquiv K QuarticNet.finThreeSuccComplement.symm) u,
      (MvPolynomial.renameEquiv K QuarticNet.finThreeSuccComplement.symm) v, ?_⟩
    rw [QuarticNet.dehomogenizeAtZero_eq_rename_coordinateOneEvaluation,
      QuarticNet.dehomogenizeAtZero_eq_rename_coordinateOneEvaluation,
      QuarticNet.dehomogenizeAtZero_eq_rename_coordinateOneEvaluation]
    simpa only [map_add, map_mul] using
      congrArg (MvPolynomial.renameEquiv K QuarticNet.finThreeSuccComplement.symm) huv
  obtain ⟨N, hN⟩ := QuarticNet.power_mul_mem_span_of_dehomogenizeAtZero_mem_span hp hq hF hdehomF
  apply (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) (X 0))) _ _).mpr
  refine ⟨⟨(Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) (X 0)) ^ N,
    Submonoid.pow_mem _ (Submonoid.mem_powers _) N⟩, ?_⟩
  change (Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) (X 0)) ^ N *
    Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) F = 0
  rw [← map_pow, ← (Ideal.Quotient.mk (Ideal.span ({p, q} : Set _))).map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hN


theorem coordinate_power_mul_mem_span_of_third_relation
    (p q r F : MvPolynomial (Fin 4) K) {a b c m : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (ha : 0 < a) (hF : F.IsHomogeneous m) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (j : Fin 4) (hglobal : r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    ∃ N : ℕ, (X j : MvPolynomial (Fin 4) K) ^ N * F ∈
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  let e : Fin 4 ≃ Fin 4 := Equiv.swap 0 j
  have hp' : (MvPolynomial.rename e p).IsHomogeneous a := hp.rename_isHomogeneous
  have hq' : (MvPolynomial.rename e q).IsHomogeneous b := hq.rename_isHomogeneous
  have hr' : (MvPolynomial.rename e r).IsHomogeneous c := hr.rename_isHomogeneous
  have hF' : (MvPolynomial.rename e F).IsHomogeneous m := hF.rename_isHomogeneous
  have hchartrel : coordinateOneEvaluation j r * coordinateOneEvaluation j F ∈ Ideal.span
      ({coordinateOneEvaluation j p, coordinateOneEvaluation j q} :
        Set (MvPolynomial {i : Fin 4 // i ≠ j} K)) := by
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hglobal
    apply Ideal.mem_span_pair.mpr
    refine ⟨coordinateOneEvaluation j u, coordinateOneEvaluation j v, ?_⟩
    simpa only [map_add, map_mul] using congrArg (coordinateOneEvaluation j) huv
  have hchartF := tripleCompleteIntersection_coordinateOne_third_regular_of_finite_algClosed
    p q r hp hq hr ha hp0 hrel j (coordinateOneEvaluation j F) hchartrel
  have hdehomF : QuarticNet.dehomogenizeAtZero (MvPolynomial.rename e F) ∈ Ideal.span
      ({QuarticNet.dehomogenizeAtZero (MvPolynomial.rename e p),
        QuarticNet.dehomogenizeAtZero (MvPolynomial.rename e q)} :
        Set (MvPolynomial (Fin 3) K)) := by
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hchartF
    apply Ideal.mem_span_pair.mpr
    refine ⟨(MvPolynomial.renameEquiv K (QuarticNet.coordinateComplementEquiv j)) u,
      (MvPolynomial.renameEquiv K (QuarticNet.coordinateComplementEquiv j)) v, ?_⟩
    dsimp [e]
    change (MvPolynomial.renameEquiv K (QuarticNet.coordinateComplementEquiv j)) u *
        QuarticNet.dehomogenizeAtZero
          (MvPolynomial.rename (Equiv.swap (0 : Fin 4) j) p) +
      (MvPolynomial.renameEquiv K (QuarticNet.coordinateComplementEquiv j)) v *
        QuarticNet.dehomogenizeAtZero
          (MvPolynomial.rename (Equiv.swap (0 : Fin 4) j) q) =
      QuarticNet.dehomogenizeAtZero
        (MvPolynomial.rename (Equiv.swap (0 : Fin 4) j) F)
    rw [QuarticNet.dehomogenizeAtZero_rename_swap_eq_rename_coordinateOneEvaluation,
      QuarticNet.dehomogenizeAtZero_rename_swap_eq_rename_coordinateOneEvaluation,
      QuarticNet.dehomogenizeAtZero_rename_swap_eq_rename_coordinateOneEvaluation]
    simpa only [map_add, map_mul] using
      congrArg (MvPolynomial.renameEquiv K (QuarticNet.coordinateComplementEquiv j)) huv
  obtain ⟨N, hN⟩ := QuarticNet.power_mul_mem_span_of_dehomogenizeAtZero_mem_span
    hp' hq' hF' hdehomF
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hN
  refine ⟨N, Ideal.mem_span_pair.mpr
    ⟨MvPolynomial.rename e.symm u, MvPolynomial.rename e.symm v, ?_⟩⟩
  have hcomp : (e.symm : Fin 4 → Fin 4) ∘ e = id := by
    funext x
    exact e.symm_apply_apply x
  have he0 : e.symm 0 = j := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (Equiv.swap_apply_right _ _).symm
  have hmap := congrArg (MvPolynomial.rename e.symm) huv
  simp only [map_add, map_mul, map_pow, MvPolynomial.rename_X,
    MvPolynomial.rename_rename] at hmap
  rw [hcomp, MvPolynomial.rename_id] at hmap
  simpa [he0] using hmap


theorem coordinate_localization_zero_of_third_relation
    (p q r F : MvPolynomial (Fin 4) K) {a b c m : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (ha : 0 < a) (hF : F.IsHomogeneous m) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (j : Fin 4) (hglobal : r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    algebraMap (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _))
      (Localization (Submonoid.powers (Ideal.Quotient.mk (Ideal.span ({p, q} :
        Set (MvPolynomial (Fin 4) K))) (X j))))
      (Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) F) = 0 := by
  obtain ⟨N, hN⟩ := coordinate_power_mul_mem_span_of_third_relation
    p q r F hp hq hr ha hF hp0 hrel j hglobal
  apply (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) (X j))) _ _).mpr
  refine ⟨⟨(Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) (X j)) ^ N,
    Submonoid.pow_mem _ (Submonoid.mem_powers _) N⟩, ?_⟩
  change (Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) (X j)) ^ N *
    Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) F = 0
  rw [← map_pow, ← (Ideal.Quotient.mk (Ideal.span ({p, q} : Set _))).map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hN


theorem third_regular_homogeneous_of_finite_algClosed
    (p q r F : MvPolynomial (Fin 4) K) {a b c m : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (ha : 0 < a) (hF : F.IsHomogeneous m) (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hglobal : r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  apply mem_of_coordinate_localization_eq_zero_of_no_irrelevant_annihilator
    (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (X 0) (X 1) (X 2) (X 3) F
  · intro x hx0 hx1 hx2 hx3
    apply two_quadrics_no_irrelevant_annihilator p q hp0 hrel x
    intro i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx2
    · exact hx3
  · intro z hz
    rcases hz with hz | hz | hz | hz
    · subst z
      exact coordinate_localization_zero_of_third_relation
        p q r F hp hq hr ha hF hp0 hrel 0 hglobal
    · subst z
      exact coordinate_localization_zero_of_third_relation
        p q r F hp hq hr ha hF hp0 hrel 1 hglobal
    · subst z
      exact coordinate_localization_zero_of_third_relation
        p q r F hp hq hr ha hF hp0 hrel 2 hglobal
    · subst z
      exact coordinate_localization_zero_of_third_relation
        p q r F hp hq hr ha hF hp0 hrel 3 hglobal


theorem third_regular_of_finite_algClosed
    (p q r : MvPolynomial (Fin 4) K) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (ha : 0 < a)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (F : MvPolynomial (Fin 4) K)
    (hglobal : r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  let I : Ideal (MvPolynomial (Fin 4) K) := Ideal.span ({p, q} : Set _)
  have hI : I.IsHomogeneous (homogeneousSubmodule (Fin 4) K) := by
    apply Ideal.homogeneous_span
    intro z hz
    rcases hz with rfl | rfl
    · exact ⟨a, hp⟩
    · exact ⟨b, hq⟩
  change F ∈ I
  rw [← sum_homogeneousComponent F]
  apply I.sum_mem
  intro d hd
  apply third_regular_homogeneous_of_finite_algClosed p q r (homogeneousComponent d F)
    hp hq hr ha (homogeneousComponent_isHomogeneous d F) hp0 hrel
  have hcomp : homogeneousComponent (c+d) (r * F) ∈ I := by
    rw [← decomposition.decompose'_apply]
    exact hI (c+d) hglobal
  rw [homogeneousComponent_mul_left hr d] at hcomp
  exact hcomp


/-- The third equation of a finite nonempty homogeneous net is regular modulo
the first two, over an arbitrary ground field.  The proof passes to the
algebraic closure, applies the chartwise regularity theorem there, and
contracts the resulting ideal membership along the faithfully flat coefficient
extension. -/
theorem third_regular_of_finite_degrees
    {k : Type u} [Field k]
    (p q r : MvPolynomial (Fin 4) k) {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (ha : 0 < a) (hc : 0 < c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hX : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)))
    (F : MvPolynomial (Fin 4) k)
    (hglobal : r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) k))) :
    F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) k)) := by
  let K := AlgebraicClosure k
  let f : k →+* K := algebraMap k K
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let J := tripleCompleteIntersectionHomogeneousIdeal
    (p.map f) (q.map f) (r.map f) (hp.map f) (hq.map f) (hr.map f)
  have hIJ : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal :=
    tripleCompleteIntersection_map_coefficientExtension p q r hp hq hr
  have hfinite : IsFinite (toBase J) :=
    tripleCompleteIntersection_isFinite_coefficientExtension (K := K) p q r hp hq hr
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
  have hp0 : p.map f ≠ 0 := by
    intro hpmap
    have hpbase : p = 0 := MvPolynomial.map_injective f f.injective (by
      simpa using hpmap)
    apply (tripleCompleteIntersection_linearIndependent_of_finite_of_nonempty
      p q r hp hq hr hX).ne_zero 0
    simp [hpbase]
  have hglobal' : r.map f * F.map f ∈ Ideal.span
      ({p.map f, q.map f} : Set (MvPolynomial (Fin 4) K)) := by
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hglobal
    apply Ideal.mem_span_pair.mpr
    refine ⟨u.map f, v.map f, ?_⟩
    simpa only [map_add, map_mul] using congrArg (MvPolynomial.map f) huv
  have hFmap : F.map f ∈ Ideal.span
      ({p.map f, q.map f} : Set (MvPolynomial (Fin 4) K)) :=
    third_regular_of_finite_algClosed (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f) ha hp0 hrel (F.map f) hglobal'
  have hpair : (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) k))).map
      (MvPolynomial.map f) = Ideal.span ({p.map f, q.map f} :
        Set (MvPolynomial (Fin 4) K)) := by
    rw [Ideal.map_span]
    apply congrArg Ideal.span
    ext x
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with rfl | rfl <;> simp
    · intro hx
      rcases hx with hx | hx
      · exact ⟨p, Or.inl rfl, hx.symm⟩
      · exact ⟨q, Or.inr rfl, hx.symm⟩
  have hmapmem : F.map f ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) k))).map
      (MvPolynomial.map f) := by
    rw [hpair]
    exact hFmap
  rw [← mvPolynomial_comap_map_coefficientExtension
    (K := K) (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) k))), Ideal.mem_comap]
  exact hmapmem

/-- The equal-degree specialization retained for the existing cubic
restriction-kernel pipeline. -/
theorem third_regular_of_finite
    {k : Type u} [Field k]
    (p q r : MvPolynomial (Fin 4) k) {n : ℕ}
    (hp : p.IsHomogeneous n) (hq : q.IsHomogeneous n) (hr : r.IsHomogeneous n)
    (hn : 0 < n)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hX : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)))
    (F : MvPolynomial (Fin 4) k)
    (hglobal : r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) k))) :
    F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) k)) :=
  third_regular_of_finite_degrees p q r hp hq hr hn hn hX F hglobal

end PfaffianDescent

import PfaffianDescent.CorayRegularPairLinearSectionAvoidance
import PfaffianDescent.CorayCubicDegreeNLinearSectionLength
import PfaffianDescent.HomogeneousQuotientMap

/-! Construct an ENTIRE rank3 ordinary cubic cut avoiding a genuine
lower-degree original divisor. All linear choices are actual finite-family
avoidance, not Bertini or supplied tangent separation. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual quotient homogeneous equation section has exactly its native vanishing
locus inside the SAME polynomial quotient scheme. No reducedness is needed. -/
theorem homogeneousQuotient_equationSection_range_iff001
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (H : MvPolynomial (Fin 4) K) {d : ℕ} (hH : H.IsHomogeneous d) (x : scheme I) :
    x ∈ Set.range (schemeQuotientMap I (I ⊔ equationIdeal H hH) le_sup_left) ↔
      Ideal.Quotient.mk I.toIdeal H ∈ x.asHomogeneousIdeal := by
  let J := I ⊔ equationIdeal H hH
  let i := schemeQuotientMap I J le_sup_left
  let j := quotientProjMap I
  have hpoint (y : scheme J) : j (i y) = quotientProjMap J y :=
    congrArg (fun f => f y) (schemeQuotientMap_comp_quotientProjMap I J le_sup_left)
  constructor
  · rintro ⟨y, rfl⟩
    have hJ : J.toIdeal ≤ (quotientProjMap J y).asHomogeneousIdeal.toIdeal :=
      (quotientProjMap_mem_range_iff J _).mp ⟨y, rfl⟩
    have hHmem : H ∈ J.toIdeal := by
      apply (show (equationIdeal H hH).toIdeal ≤ J.toIdeal from le_sup_right)
      exact Ideal.subset_span (Set.mem_singleton H)
    have hraw := hJ hHmem
    rw [← hpoint y] at hraw
    exact hraw
  · intro hHmem
    have hI : I.toIdeal ≤ (j x).asHomogeneousIdeal.toIdeal :=
      (quotientProjMap_mem_range_iff I _).mp ⟨x, rfl⟩
    have hJ : J.toIdeal ≤ (j x).asHomogeneousIdeal.toIdeal := by
      rw [show J.toIdeal = I.toIdeal ⊔ (equationIdeal H hH).toIdeal from
        HomogeneousIdeal.toIdeal_sup I (equationIdeal H hH)]
      refine sup_le hI ?_
      change Ideal.span ({H} : Set (MvPolynomial (Fin 4) K)) ≤ _
      apply Ideal.span_le.mpr
      intro f hf
      rcases Set.mem_singleton_iff.mp hf with rfl
      exact hHmem
    obtain ⟨y, hy⟩ := (quotientProjMap_mem_range_iff J (j x)).mpr hJ
    refine ⟨y, j.isClosedEmbedding.injective ?_⟩
    exact (hpoint y).trans hy

/-- An actual nonzero section on the smooth cubic and its actual point
internally yield TWO linear equations whose rank3 entire cut avoids that
section. The original point is also avoided by the first linear equation. -/
theorem cubic_nonzeroSection_exists_rankThree_linearCut_avoiding_divisor001
    [Infinite K]
    (p s : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (a : ℕ) (hs : s.IsHomogeneous a)
    (hnot : s ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (x : scheme (projectiveIntersectionIdeal p s hp hs)) :
    ∃ (H G : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1) (hG : G.IsHomogeneous 1),
      Ideal.Quotient.mk (projectiveIntersectionIdeal p s hp hs).toIdeal H ∉ x.asHomogeneousIdeal ∧
      let C := projectiveIntersectionIdeal p H hp hH
      let Z := C ⊔ equationIdeal G hG
      ∃ hFiniteZ : IsFinite (toBase Z),
        letI := hFiniteZ
        finiteSchemeRank (toBase Z) = 3 ∧
          ∀ z : scheme Z, Ideal.Quotient.mk C.toIdeal s ∉
            ((schemeQuotientMap C Z le_sup_left) z).asHomogeneousIdeal := by
  classical
  have hs0 : s ≠ 0 := by
    intro h
    apply hnot
    rw [h]
    exact Ideal.zero_mem _
  have hRel := isRelPrime_of_smooth_cubic_and_not_mem p s hp hp0 hnot
  obtain ⟨H, hH, hHregular, hHavoid⟩ :=
    regular_pair_exists_linear_nonzerodivisor_avoiding_finite_projective_family
      p s hp hs hp0 hRel (fun _ : Unit => x)
  have hHnot : H ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro hmem
    apply hHavoid ()
    have hpLow : Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ≤
        (projectiveIntersectionIdeal p s hp hs).toIdeal := le_sup_left
    have hzero : Ideal.Quotient.mk (projectiveIntersectionIdeal p s hp hs).toIdeal H = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hpLow hmem)
    rw [hzero]
    exact x.asHomogeneousIdeal.toIdeal.zero_mem
  have hH0 : H ≠ 0 := by
    intro h
    apply hHnot
    rw [h]
    exact Ideal.zero_mem _
  let C := projectiveIntersectionIdeal p H hp hH
  let T := C ⊔ equationIdeal s hs
  have hT_eq : T = tripleCompleteIntersectionHomogeneousIdeal p s H hp hs hH := by
    apply HomogeneousIdeal.toIdeal_injective
    dsimp only [T, C]
    rw [HomogeneousIdeal.toIdeal_sup, projectiveIntersectionIdeal_toIdeal,
      tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
    change Ideal.span ({p, H} : Set (MvPolynomial (Fin 4) K)) ⊔
      Ideal.span ({s} : Set (MvPolynomial (Fin 4) K)) =
        Ideal.span ({p, s, H} : Set (MvPolynomial (Fin 4) K))
    rw [← Ideal.span_union]
    congr 1
    ext y
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  letI : IsFinite (toBase T) := by
    rw [hT_eq]
    exact cubic_degree_n_linear_section_finite p s H hp hs hH hp0 hs0 hRel hHregular
  letI : IsLocallyArtinian (scheme T) := IsLocallyArtinian.of_locallyQuasiFinite (toBase T)
  letI : CompactSpace (scheme T) := QuasiCompact.compactSpace_of_compactSpace (toBase T)
  letI : IsArtinianScheme (scheme T) := ⟨⟩
  letI : Finite (scheme T) := inferInstance
  let iT := schemeQuotientMap C T le_sup_left
  obtain ⟨G, hG, hGregular, hGavoid⟩ :=
    regular_pair_exists_linear_nonzerodivisor_avoiding_finite_projective_family
      p H hp hH hp0 (isRelPrime_of_smooth_cubic_and_not_mem p H hp hp0 hHnot) iT
  let Z := C ⊔ equationIdeal G hG
  have hZ_eq : Z = tripleCompleteIntersectionHomogeneousIdeal p H G hp hH hG := by
    apply HomogeneousIdeal.toIdeal_injective
    dsimp only [Z, C]
    rw [HomogeneousIdeal.toIdeal_sup, projectiveIntersectionIdeal_toIdeal,
      tripleCompleteIntersectionHomogeneousIdeal_toIdeal]
    change Ideal.span ({p, H} : Set (MvPolynomial (Fin 4) K)) ⊔
      Ideal.span ({G} : Set (MvPolynomial (Fin 4) K)) =
        Ideal.span ({p, H, G} : Set (MvPolynomial (Fin 4) K))
    rw [← Ideal.span_union]
    congr 1
    ext y
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  letI hFiniteZ : IsFinite (toBase Z) := by
    rw [hZ_eq]
    exact cubic_degree_n_linear_section_finite p H G hp hH hG hp0 hH0
        (isRelPrime_of_smooth_cubic_and_not_mem p H hp hp0 hHnot) hGregular
  have hRank : finiteSchemeRank (toBase Z) = 3 := by
    have hTransfer : ∀ W : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
        W = tripleCompleteIntersectionHomogeneousIdeal p H G hp hH hG →
        ∀ hFinite : IsFinite (toBase W), letI := hFinite
          finiteSchemeRank (toBase W) = 3 := by
      intro W hW
      subst W
      intro hFinite
      simpa only [Nat.mul_one] using
        cubic_degree_n_linear_section_length_three_mul p H G hp hH hG hp0 hH0
          (isRelPrime_of_smooth_cubic_and_not_mem p H hp hp0 hHnot) hGregular
    exact hTransfer Z hZ_eq hFiniteZ
  refine ⟨H, G, hH, hG, hHavoid (), hFiniteZ, hRank, ?_⟩
  intro z hsMem
  let iZ := schemeQuotientMap C Z le_sup_left
  have hGmem : Ideal.Quotient.mk C.toIdeal G ∈ (iZ z).asHomogeneousIdeal :=
    (homogeneousQuotient_equationSection_range_iff001 C G hG (iZ z)).mp ⟨z, rfl⟩
  obtain ⟨t, ht⟩ :=
    (homogeneousQuotient_equationSection_range_iff001 C s hs (iZ z)).mpr hsMem
  apply hGavoid t
  change Ideal.Quotient.mk C.toIdeal G ∈ (iT t).asHomogeneousIdeal
  rw [ht]
  exact hGmem

end PfaffianDescent.Coray

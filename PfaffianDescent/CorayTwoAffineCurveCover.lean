import PfaffianDescent.CoraySelectedPrimeCurveHilbertLinearity
import PfaffianDescent.CorayRegularPairLinearSectionAvoidance
import PfaffianDescent.HomogeneousQuotientMap
import PfaffianDescent.CorayFourAffineCoverCohomologicalDimension

/-! Source-only: actual two-affine-open cover of the literal p/q curve,
including reducible and nonreduced curves, with native H² vanishing. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual quotient hyperplane section has exactly its native vanishing
locus inside the SAME polynomial quotient scheme. No reducedness is needed. -/
theorem homogeneousQuotient_hyperplaneSection_range_iff
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1) (x : scheme I) :
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

/-- Two actual degree-one affine charts cover the literal smooth-cubic/q
intersection. The first section is finite by genuine regular-pair selection;
the second form avoids that SAME finite section. No component, integral,
reduced, finite-cut or cover certificate is an original hypothesis. -/
theorem projectiveIntersection_exists_two_affine_open_cover
    [Infinite K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    ∃ U : Fin 2 → (scheme (projectiveIntersectionIdeal p q hp hq)).Opens,
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  have hrel := isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot
  obtain ⟨H, hH, hregular, _⟩ :=
    regular_pair_exists_linear_nonzerodivisor_avoiding_finite_projective_family
      p q hp hq hp0 hrel (fun e : Empty => nomatch e)
  have hq0 : q ≠ 0 := by
    intro h
    apply hnot
    rw [h]
    exact Ideal.zero_mem _
  let J := I ⊔ equationIdeal H hH
  let i := schemeQuotientMap I J le_sup_left
  letI : IsFinite (toBase J) := selectedProjectiveComponent_regular_linearSection_isFinite
    p q H hp hq hH hp0 hq0 hrel hregular I le_rfl
  obtain ⟨z, hz, havoid⟩ := finite_scheme_projective_image_avoiding_linear I (toBase J) i
  let w := Ideal.Quotient.mk I.toIdeal H
  have hw : w ∈ grading I 1 := polynomial_class_mem_grading I H hH
  let U : Fin 2 → X.Opens := fun j => if j = 0 then
    Proj.basicOpen (grading I) w else Proj.basicOpen (grading I) z
  refine ⟨U, ?_, ?_⟩
  · intro j
    dsimp only [U]
    split_ifs
    · exact Proj.isAffineOpen_basicOpen (grading I) w (m := 1) hw (by decide)
    · exact Proj.isAffineOpen_basicOpen (grading I) z (m := 1) hz (by decide)
  · apply top_unique
    intro x _
    by_cases hmem : w ∈ x.asHomogeneousIdeal
    · obtain ⟨y, hy⟩ := (homogeneousQuotient_hyperplaneSection_range_iff I H hH x).mpr hmem
      have hx : x ∈ U 1 := by
        change x ∈ Proj.basicOpen (grading I) z
        change z ∉ x.asHomogeneousIdeal
        rw [← hy]
        exact havoid y
      exact (le_iSup U 1) hx
    · have hx : x ∈ U 0 := by
        change x ∈ Proj.basicOpen (grading I) w
        exact hmem
      exact (le_iSup U 0) hx

/-- Native cohomology on the actual p/q scheme vanishes in every degree
at least two for EVERY quasicoherent module. Its actual two-affine cover,
local noetherianity and separatedness are derived internally. -/
theorem projectiveIntersection_quasicoherent_cohomology_subsingleton_ge_two
    [Infinite K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [HasExt.{u} (scheme (projectiveIntersectionIdeal p q hp hq)).Modules]
    (M : (scheme (projectiveIntersectionIdeal p q hp hq)).Modules)
    [M.IsQuasicoherent] (k : ℕ) (hk : 2 ≤ k) :
    Subsingleton (schemeModuleCohomology
      (scheme (projectiveIntersectionIdeal p q hp hq)) M k) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (toBase I)
  letI : X.IsSeparated := inferInstanceAs ((Proj (grading I)).IsSeparated)
  obtain ⟨U, hU, hcover⟩ := projectiveIntersection_exists_two_affine_open_cover
    p q hp hp0 n hq hnot
  exact schemeModuleCohomology_subsingleton_of_finiteAffineCover M 1 U hU hcover k hk

end PfaffianDescent.Coray

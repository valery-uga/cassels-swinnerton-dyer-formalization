import PfaffianDescent.VoisinGenericCubicSmooth
import PfaffianDescent.VoisinGenericSplitEtale

/-!
# One smooth transverse split witness over the generic cubic

This packages the independently checked smoothness, length, étaleness, and
quadratic coordinate dimensions for the same universal cubic equation.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem generic_smooth_split_twelve_point_witness
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let q : MvPolynomial (Fin 4) L := X 1 * X 2
    let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
    let hp := cubic_toMvPolynomial_isHomogeneous_three ((genericCubicTensor K).map φ)
    let hq := (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
    let hr := (isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3))
    let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ hfinite : IsFinite (toBase I),
        letI : IsFinite (toBase I) := hfinite
        finiteSchemeRank (toBase I) = 12 ∧ Etale (toBase I) ∧
          Module.finrank L (grading I 2) = 8 := by
  dsimp only
  refine ⟨genericCubicTensor_smooth_baseChange K φ, ?_⟩
  letI := generic_split_intersection_finite K φ
  exact ⟨inferInstance, generic_split_intersection_rank_twelve K φ,
    generic_split_intersection_etale K φ,
    generic_split_intersection_quadratic_quotient_rank_eight K φ⟩

/-- The twelve generic intersection roots are twelve distinct rational
points of the actual projective complete-intersection scheme. -/
theorem exists_generic_split_twelve_distinct_scheme_points
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let q : MvPolynomial (Fin 4) L := X 1 * X 2
    let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
    let hp := cubic_toMvPolynomial_isHomogeneous_three ((genericCubicTensor K).map φ)
    let hq := (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
    let hr := (isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3))
    let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    ∃ t : (Fin 2 × Fin 2 × Fin 3) → (Spec (.of L) ⟶ scheme I),
      (∀ u, t u ≫ toBase I =
        Spec.map (CommRingCat.ofHom (RingHom.id L))) ∧
      Function.Injective t := by
  dsimp only
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let q : MvPolynomial (Fin 4) L := X 1 * X 2
  let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let hp := cubic_toMvPolynomial_isHomogeneous_three ((genericCubicTensor K).map φ)
  let hq : q.IsHomogeneous 2 := (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
  let hr : r.IsHomogeneous 2 := (isHomogeneous_X L 3).mul
    (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
      (isHomogeneous_X L 3))
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  obtain ⟨x, hinj, hzero, hform, -⟩ :=
    exists_generic_four_line_root_triples K φ
  have hform' : ∀ i j k, ∃ t : L,
      x i j k = t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j := by
    intro i j k
    obtain ⟨t, ht⟩ := hform i j k
    refine ⟨t, ?_⟩
    rwa [genericFourLineBase_baseChange_eq K φ,
      genericFourLineDirection_baseChange_eq K φ i j] at ht
  have hroots : ∀ i j k,
      p.eval (x i j k) = 0 ∧ q.eval (x i j k) = 0 ∧
        r.eval (x i j k) = 0 := by
    intro i j k
    obtain ⟨s, hs⟩ := hform' i j k
    have hsplit := standard_split_quadrics_zero_on_line i j s
    have hpzero := hzero i j k
    rw [hs] at hpzero
    have hev := Cubic.eval_toMvPolynomial (RingHom.id L)
      ((genericCubicTensor K).map φ)
      (s • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j)
    change p.eval (s • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) =
      ((genericCubicTensor K).map φ).eval
        (s • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) at hev
    rw [hs]
    exact ⟨hev.trans hpzero, hsplit.1, hsplit.2⟩
  have hI : ∀ i j k, ∀ f ∈ I.toIdeal, f.eval (x i j k) = 0 := by
    intro i j k
    exact tripleCompleteIntersection_vector_zero_of_generators
      p q r hp hq hr (x i j k)
        (hroots i j k).1 (hroots i j k).2.1 (hroots i j k).2.2
  exact exists_twelve_distinct_scheme_points_of_sheared_line_roots
    I (Pi.single 0 1 : Fin 4 → L) (by simp) x hinj hform' hI

/-- The actual global algebra of the generic split intersection is the
product of twelve copies of the algebraically closed coefficient field. -/
theorem generic_split_intersection_coordinate_algebra_equiv_pi
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let q : MvPolynomial (Fin 4) L := X 1 * X 2
    let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
    let hp := cubic_toMvPolynomial_isHomogeneous_three ((genericCubicTensor K).map φ)
    let hq := (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
    let hr := (isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3))
    let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
    letI := generic_split_intersection_finite K φ
    letI := finiteSchemeCoefficientAlgebra (toBase I)
    Nonempty (Γ(scheme I, ⊤) ≃ₐ[L] (Fin 12 → L)) := by
  classical
  dsimp only
  let I := tripleCompleteIntersectionHomogeneousIdeal
    ((genericCubicTensor K).map φ).toMvPolynomial
    (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))
    (cubic_toMvPolynomial_isHomogeneous_three _)
    ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
    ((isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3)))
  letI : IsFinite (toBase I) := generic_split_intersection_finite K φ
  obtain ⟨t, hbase, hinj⟩ :=
    exists_generic_split_twelve_distinct_scheme_points K φ
  let e : Fin 12 ≃ Fin 2 × Fin 2 × Fin 3 :=
    (Fintype.equivFinOfCardEq (by decide :
      Fintype.card (Fin 2 × Fin 2 × Fin 3) = 12)).symm
  let x : Fin 12 → (Spec (.of L) ⟶ scheme I) := t ∘ e
  have hxbase : ∀ i, x i ≫ toBase I =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    intro i
    exact hbase (e i)
  have hxinj : Function.Injective x := hinj.comp e.injective
  letI := finiteSchemeCoefficientAlgebra (toBase I)
  exact ⟨finiteSchemeCoefficient_equiv_pi_of_full_rational_points
    (toBase I) x hxbase hxinj
    (generic_split_intersection_rank_twelve K φ)⟩

end PfaffianDescent

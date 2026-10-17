import AllCharacteristics.HomogeneousProjectiveAmbient
import AllCharacteristics.NormalizedChartGeneration
import AllCharacteristics.PolynomialQuotientBaseChange

/-!
# Polynomial presentation of an ordinary ambient projective chart

On the chart where `X j` is invertible, normalized coordinates identify the
degree-zero localization of the homogeneous polynomial ring with the
polynomial quotient by `X j - 1`. This direct presentation avoids passing
through the homogeneous quotient by the zero ideal.
-/

open MvPolynomial HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective

universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ R

/-- Set the distinguished homogeneous coordinate equal to one. -/
noncomputable def ambientChartPresentationIdeal (j : σ) : Ideal (MvPolynomial σ R) :=
  Ideal.span {MvPolynomial.X j - 1}

/-- The normalized degree-one coordinate in an ordinary ambient chart. -/
noncomputable def ambientChartCoordinate (j i : σ) : Away 𝒜 (MvPolynomial.X j) :=
  GradedChart.normalized 𝒜 (MvPolynomial.isHomogeneous_X R j)
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i)

/-- Evaluate polynomials at the normalized ambient coordinates. -/
noncomputable def ambientChartEvaluation (j : σ) :
    MvPolynomial σ R →+* Away 𝒜 (MvPolynomial.X j) :=
  MvPolynomial.eval₂Hom (GradedChart.baseMap 𝒜 (z := MvPolynomial.X j))
    (ambientChartCoordinate j)

/-- Homogeneous evaluation is the corresponding degree-zero fraction. -/
theorem ambientChartEvaluation_homogeneous
    (j : σ) (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    ambientChartEvaluation j p =
      Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R j) d p (by simpa using hp) := by
  let hx : MvPolynomial.X j ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R j
  apply HomogeneousLocalization.val_injective
  refine (GradedChart.val_eval₂_normalized 𝒜
    hx MvPolynomial.X
    (MvPolynomial.isHomogeneous_X R) p hp).trans ?_
  have he : p.eval₂ (algebraMap R (MvPolynomial σ R)) MvPolynomial.X = p := by
    change p.eval₂ MvPolynomial.C MvPolynomial.X = p
    exact MvPolynomial.eval₂_eta p
  rw [he]
  have hp' : p ∈ 𝒜 (d • 1) := by simpa using hp
  change _ = (Away.mk 𝒜 hx d p hp').val
  rw [Away.val_mk]
  simp only [Localization.mk_pow, one_pow, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul, mul_one]
  rfl

/-- The normalized coordinates generate the entire ambient chart ring. -/
theorem ambientChartEvaluation_surjective (j : σ) :
    Function.Surjective (ambientChartEvaluation (R := R) (σ := σ) j) := by
  intro z
  let hx : MvPolynomial.X j ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R j
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective 𝒜 hx z
  have hp' : p.IsHomogeneous n := by simpa using hp
  exact ⟨p, ambientChartEvaluation_homogeneous j p hp'⟩

/-- Evaluation of an ambient chart in the polynomial quotient with `X j = 1`. -/
noncomputable def ambientChartToPresentation (j : σ) :
    Away 𝒜 (MvPolynomial.X j) →+*
      MvPolynomial σ R ⧸ ambientChartPresentationIdeal j :=
  GradedChart.liftCoordinateOne 𝒜 (MvPolynomial.X j)
    (Ideal.Quotient.mk (ambientChartPresentationIdeal j)) (by
      change Ideal.Quotient.mk (ambientChartPresentationIdeal j) (MvPolynomial.X j) =
        Ideal.Quotient.mk (ambientChartPresentationIdeal j) 1
      apply Ideal.Quotient.eq.mpr
      exact Ideal.subset_span (Set.mem_singleton _))

/-- The chart-to-presentation map preserves base coefficients. -/
theorem ambientChartToPresentation_baseMap (j : σ) (r : R) :
    ambientChartToPresentation j
      (GradedChart.baseMap 𝒜 (z := MvPolynomial.X j) r) =
      Ideal.Quotient.mk (ambientChartPresentationIdeal j) (MvPolynomial.C r) :=
  GradedChart.liftCoordinateOne_baseMap 𝒜 (MvPolynomial.X j)
    (Ideal.Quotient.mk (ambientChartPresentationIdeal j)) _ r

/-- A normalized ambient coordinate maps to its polynomial class. -/
theorem ambientChartToPresentation_coordinate (j i : σ) :
    ambientChartToPresentation (R := R) (σ := σ) j (ambientChartCoordinate (R := R) j i) =
      Ideal.Quotient.mk (ambientChartPresentationIdeal (R := R) (σ := σ) j)
        (MvPolynomial.X i) :=
  GradedChart.liftCoordinateOne_normalized 𝒜 (MvPolynomial.X j)
    (Ideal.Quotient.mk (ambientChartPresentationIdeal j)) _
    (MvPolynomial.isHomogeneous_X R j) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i)

/-- Normalized evaluation followed by the polynomial presentation is the
quotient map. -/
theorem ambientChartToPresentation_eval (j : σ) (p : MvPolynomial σ R) :
    ambientChartToPresentation (R := R) (σ := σ) j (ambientChartEvaluation j p) =
      Ideal.Quotient.mk (ambientChartPresentationIdeal j) p := by
  have h : (ambientChartToPresentation (R := R) (σ := σ) j).comp
      (ambientChartEvaluation (R := R) (σ := σ) j) =
      Ideal.Quotient.mk (ambientChartPresentationIdeal j) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, ambientChartEvaluation, MvPolynomial.eval₂Hom_C]
      exact ambientChartToPresentation_baseMap j r
    · intro i
      simp only [RingHom.comp_apply, ambientChartEvaluation, MvPolynomial.eval₂Hom_X']
      exact ambientChartToPresentation_coordinate j i
  exact DFunLike.congr_fun h p

/-- The distinguished normalized coordinate is one. -/
theorem ambientChartCoordinate_self (j : σ) : ambientChartCoordinate (R := R) j j = 1 :=
  GradedChart.normalized_self 𝒜 (MvPolynomial.isHomogeneous_X R j)

/-- The only relation among normalized ambient coordinates is `X j = 1`. -/
theorem ambientChartEvaluation_ker (j : σ) :
    RingHom.ker (ambientChartEvaluation (R := R) (σ := σ) j) =
      ambientChartPresentationIdeal j := by
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg (ambientChartToPresentation (R := R) (σ := σ) j)
      (show ambientChartEvaluation j p = 0 from hp)
    exact (ambientChartToPresentation_eval j p).symm.trans (h.trans (map_zero _))
  · apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    change (MvPolynomial.X j - 1 : MvPolynomial σ R).eval₂
      (GradedChart.baseMap 𝒜 (z := MvPolynomial.X j))
      (ambientChartCoordinate j) = 0
    rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_one, ambientChartCoordinate_self, sub_self]

/-- An ordinary ambient projective coordinate chart is the polynomial
quotient by `X j - 1`. -/
noncomputable def ambientChartPresentationEquiv (j : σ) :
    (MvPolynomial σ R ⧸ ambientChartPresentationIdeal j) ≃+*
      Away 𝒜 (MvPolynomial.X j) :=
  (Ideal.quotEquivOfEq (ambientChartEvaluation_ker j).symm).trans
    (RingHom.quotientKerEquivOfSurjective (ambientChartEvaluation_surjective j))

/-- The presentation equivalence sends each polynomial class to its
normalized-coordinate evaluation. -/
theorem ambientChartPresentationEquiv_mk (j : σ) (p : MvPolynomial σ R) :
    ambientChartPresentationEquiv j
      (Ideal.Quotient.mk (ambientChartPresentationIdeal j) p) =
      ambientChartEvaluation j p := by
  exact (congrArg
    (RingHom.quotientKerEquivOfSurjective (ambientChartEvaluation_surjective j))
    (Ideal.quotEquivOfEq_mk (ambientChartEvaluation_ker j).symm p)).trans
    (RingHom.quotientKerEquivOfSurjective_apply_mk
      (ambientChartEvaluation_surjective j) p)

end HomogeneousProjective
end AllCharacteristics

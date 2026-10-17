import PfaffianDescent.FiniteAffineLinearSystemTriple
import PfaffianDescent.ProjectiveDehomogenizedArtinian
import PfaffianDescent.HomogeneousIdealPieces
import PfaffianDescent.TripleCompleteIntersectionLength

/-! The missing finite-triple extraction from the FULL quadratic series.
This leaf is over an infinite field; arbitrary-field descent is separate. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The base ideal of ALL members of one homogeneous quadratic linear
system, including systems defined by actual evaluation on nonreduced Z. -/
def quadraticSystemBaseLocusIdeal
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hW : ∀ q ∈ W, q.IsHomogeneous 2) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) :=
  ⟨Ideal.span (W : Set (MvPolynomial (Fin 4) K)), by
    apply Ideal.homogeneous_span
    intro q hq
    exact ⟨2, hW q hq⟩⟩

private theorem quadraticSystemBaseLocus_chart_ideal
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hW : ∀ q ∈ W, q.IsHomogeneous 2) (j : Fin 4) :
    (quadraticSystemBaseLocusIdeal W hW).toIdeal.map
      (projectiveDehomogenizedChartMap j).toRingHom =
    finiteAffineLinearSystemFullIdeal
      ((projectiveDehomogenizedChartMap j).toLinearMap.comp W.subtype) := by
  change (Ideal.span (W : Set (MvPolynomial (Fin 4) K))).map
    (projectiveDehomogenizedChartMap j).toRingHom = _
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q.val, q.property, rfl⟩

/-- From a finite FULL quadratic base locus, select THREE actual quadrics in
that system with finite projective intersection. Its avoidance witnesses are
constructed on all four actual normalized charts. -/
theorem exists_finite_triple_of_finite_full_quadratic_system [Infinite K]
    (W : Submodule K (MvPolynomial (Fin 4) K))
    (hW : ∀ q ∈ W, q.IsHomogeneous 2)
    [IsFinite (toBase (quadraticSystemBaseLocusIdeal W hW))] :
    ∃ q : Fin 3 → W,
      IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (q 0).val (q 1).val (q 2).val
        (hW _ (q 0).property) (hW _ (q 1).property) (hW _ (q 2).property))) := by
  let φ : Fin 4 → (W →ₗ[K] MvPolynomial (Fin 3) K) := fun j =>
    (projectiveDehomogenizedChartMap j).toLinearMap.comp W.subtype
  have hfull : ∀ j, IsArtinianRing
      (MvPolynomial (Fin 3) K ⧸ finiteAffineLinearSystemFullIdeal (φ j)) := by
    intro j
    rw [← quadraticSystemBaseLocus_chart_ideal W hW j]
    exact projectiveDehomogenizedChart_isArtinian_of_finite (quadraticSystemBaseLocusIdeal W hW) j
  obtain ⟨q, hq⟩ := exists_three_sections_of_full_chart_artinian φ hfull
  refine ⟨q, ?_⟩
  let T := tripleCompleteIntersectionHomogeneousIdeal
    (q 0).val (q 1).val (q 2).val
    (hW _ (q 0).property) (hW _ (q 1).property) (hW _ (q 2).property)
  apply projective_isFinite_of_dehomogenizedCharts_isArtinian T
  intro j
  have hT : T.toIdeal.map (projectiveDehomogenizedChartMap j).toRingHom =
      finiteAffineLinearSystemSelectedIdeal (φ j) q := by
    rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal, tripleCompleteIntersectionIdeal,
      Ideal.map_span]
    apply congrArg Ideal.span
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      rcases hf with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨(q 0).val, Or.inl rfl, rfl⟩
      · exact ⟨(q 1).val, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨(q 2).val, Or.inr (Or.inr rfl), rfl⟩
  rw [hT]
  exact hq j

/-- All homogeneous quadrics of a homogeneous ideal, without reducing it. -/
def quadraticFullLinearSystem
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  I.toIdeal.restrictScalars K ⊓ homogeneousSubmodule (Fin 4) K 2

/-- The full quadratic base ideal of this homogeneous ideal. -/
def quadraticFullBaseLocusIdeal
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) :=
  quadraticSystemBaseLocusIdeal (quadraticFullLinearSystem I) (fun _ hq => hq.2)

/-- Homogeneous-ideal specialization of the full-system extraction. -/
theorem exists_finite_triple_of_finite_full_quadratic_base_locus [Infinite K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    [IsFinite (toBase (quadraticFullBaseLocusIdeal I))] :
    ∃ q : Fin 3 → quadraticFullLinearSystem I,
      IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (q 0).val (q 1).val (q 2).val
        (q 0).property.2 (q 1).property.2 (q 2).property.2)) := by
  letI : IsFinite (toBase (quadraticSystemBaseLocusIdeal
      (quadraticFullLinearSystem I) (fun _ hq => hq.2))) := inferInstanceAs
    (IsFinite (toBase (quadraticFullBaseLocusIdeal I)))
  exact exists_finite_triple_of_finite_full_quadratic_system
    (quadraticFullLinearSystem I) (fun _ hq => hq.2)

end PfaffianDescent

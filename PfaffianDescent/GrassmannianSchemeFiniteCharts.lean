import PfaffianDescent.GrassmannianSchemeBasicCharts
import Mathlib.RingTheory.Ideal.Span

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {m n : ℕ}

/-- A scheme point has a finite cover by basic graph charts whose denominators generate the unit ideal. -/
theorem grassmannian_scheme_point_exists_finite_charts
    (f : GrassmannianAlgebraPoint K A m n) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ a ∈ s, ∃ (σ : Equiv.Perm (Fin m ⊕ Fin n))
        (T : Matrix (Fin n) (Fin m) (Localization.Away a)),
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ f.1 =
          (grassmannianChartAlgebraPoint K (Localization.Away a) m n σ T).1 := by
  classical
  let V : Set A := {a | ∃ (σ : Equiv.Perm (Fin m ⊕ Fin n))
      (T : Matrix (Fin n) (Fin m) (Localization.Away a)),
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ f.1 =
        (grassmannianChartAlgebraPoint K (Localization.Away a) m n σ T).1}
  have hV : Ideal.span V = ⊤ := by
    by_contra h
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal (Ideal.span V) h
    let p : PrimeSpectrum A := ⟨I, hI.isPrime⟩
    obtain ⟨a, ha, σ, T, hT⟩ := grassmannian_scheme_point_exists_basic_chart K f p
    exact ha (hle (Ideal.subset_span (show a ∈ V from ⟨σ, T, hT⟩)))
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite V).mp hV
  exact ⟨s, hspan, fun a ha => hs ha⟩

/-- Finite graph-coordinate data for an actual scheme point. -/
structure GrassmannianSchemeFiniteChartData (f : GrassmannianAlgebraPoint K A m n) where
  denominators : Finset A
  span_eq_top : Ideal.span (denominators : Set A) = ⊤
  permutation : denominators → Equiv.Perm (Fin m ⊕ Fin n)
  matrix : ∀ a : denominators, Matrix (Fin n) (Fin m) (Localization.Away a.1)
  point_eq : ∀ a : denominators,
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.1))) ≫ f.1 =
      (grassmannianChartAlgebraPoint K (Localization.Away a.1) m n (permutation a) (matrix a)).1

lemma grassmannianSchemeFiniteChartData_nonempty
    (f : GrassmannianAlgebraPoint K A m n) : Nonempty (GrassmannianSchemeFiniteChartData K f) := by
  classical
  obtain ⟨s, hs, h⟩ := grassmannian_scheme_point_exists_finite_charts K f
  choose σ T hT using fun a : s => h a.1 a.2
  exact ⟨⟨s, hs, σ, T, hT⟩⟩

noncomputable def grassmannianSchemeFiniteChartData
    (f : GrassmannianAlgebraPoint K A m n) : GrassmannianSchemeFiniteChartData K f :=
  Classical.choice (grassmannianSchemeFiniteChartData_nonempty K f)

end
end PfaffianDescent

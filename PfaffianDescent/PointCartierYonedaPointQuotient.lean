import PfaffianDescent.PointCartierYonedaRetractionComparison
import PfaffianDescent.PointCartierYonedaAmbientKoszul

/-! # The canonical map between ambient and surface point quotients -/

noncomputable section

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Abelian

universe u

variable {R : Type u} [CommRing R]

theorem pointCartierYoneda_surface_first_mem (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) :
    Ideal.Quotient.mk (Ideal.span {p}) f ∈ Ideal.span
      ({Ideal.Quotient.mk (Ideal.span {p}) g,
        Ideal.Quotient.mk (Ideal.span {p}) h} : Set (R ⧸ Ideal.span {p})) := by
  rw [← twoGeneratorLast_range]
  refine ⟨(-Ideal.Quotient.mk (Ideal.span {p}) b * Ideal.Quotient.mk (Ideal.span {p}) (v⁻¹ : Rˣ),
    -Ideal.Quotient.mk (Ideal.span {p}) c * Ideal.Quotient.mk (Ideal.span {p}) (v⁻¹ : Rˣ)), ?_⟩
  change Ideal.Quotient.mk (Ideal.span {p}) g *
      (-Ideal.Quotient.mk (Ideal.span {p}) b * Ideal.Quotient.mk (Ideal.span {p}) (v⁻¹ : Rˣ)) +
    Ideal.Quotient.mk (Ideal.span {p}) h *
      (-Ideal.Quotient.mk (Ideal.span {p}) c * Ideal.Quotient.mk (Ideal.span {p}) (v⁻¹ : Rˣ)) =
        Ideal.Quotient.mk (Ideal.span {p}) f
  have hrel := pointCartierYonedaUnitRetraction_relation f g h p v b c heq
  linear_combination -hrel

theorem pointCartierYonedaPointQuotient_kernel (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) :
    Ideal.span ({f, g, h} : Set R) ≤ LinearMap.ker
      (((Ideal.Quotient.mkₐ R (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span {p}) g,
          Ideal.Quotient.mk (Ideal.span {p}) h} : Set (R ⧸ Ideal.span {p})))).toLinearMap).comp
        (Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap) := by
  have hmem : Ideal.span ({f, g, h} : Set R) ≤
      Ideal.comap (Ideal.Quotient.mk (Ideal.span {p})) (Ideal.span
        ({Ideal.Quotient.mk (Ideal.span {p}) g,
          Ideal.Quotient.mk (Ideal.span {p}) h} : Set (R ⧸ Ideal.span {p}))) := by
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxf | hxg | hxh
    · rw [hxf]
      exact pointCartierYoneda_surface_first_mem f g h p v b c heq
    · rw [hxg]
      exact Ideal.subset_span (by simp)
    · rw [hxh]
      exact Ideal.subset_span (by simp)
  intro x hx
  change Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {p}) x) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem hx)

/-- The map induced by the actual ambient point augmentation followed by
the two-parameter surface point quotient. -/
def pointCartierYonedaPointQuotientMap (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) :
    (R ⧸ Ideal.span ({f, g, h} : Set R)) →ₗ[R]
      ((R ⧸ Ideal.span {p}) ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.span {p}) g,
          Ideal.Quotient.mk (Ideal.span {p}) h} : Set (R ⧸ Ideal.span {p}))) :=
  (Ideal.span ({f, g, h} : Set R)).liftQ
    (((Ideal.Quotient.mkₐ R (Ideal.span
      ({Ideal.Quotient.mk (Ideal.span {p}) g,
        Ideal.Quotient.mk (Ideal.span {p}) h} : Set (R ⧸ Ideal.span {p})))).toLinearMap).comp
      (Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap)
    (pointCartierYonedaPointQuotient_kernel f g h p v b c heq)

@[simp]
theorem pointCartierYonedaPointQuotientMap_mk (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) (x : R) :
    pointCartierYonedaPointQuotientMap f g h p v b c heq
      (Ideal.Quotient.mk (Ideal.span ({f, g, h} : Set R)) x) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {p}) x) := rfl

end PfaffianDescent

import AllCharacteristics.GradedChartOverlap

/-!
# Extending a chart homomorphism to an overlap

For two degree-one coordinates, the product chart is the localization of the
first chart at their normalized ratio. A chart homomorphism therefore extends
to this overlap whenever that ratio maps to a unit.
-/

open HomogeneousLocalization
namespace AllCharacteristics
namespace GradedChart
universe u v w
variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]
variable {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)

/-- For degree-one coordinates, the element inverted on an overlap is their normalized ratio. -/
theorem isLocalizationElem_eq_normalized :
    Away.isLocalizationElem hf hg = normalized 𝒜 hf g hg := by
  apply val_injective
  simp only [Away.isLocalizationElem, normalized, Away.val_mk, pow_one]

/-- A chart homomorphism extends to the product chart if the second coordinate ratio is a unit. -/
theorem exists_overlap_hom (φ : Away 𝒜 f →+* B) (hu : IsUnit (φ (normalized 𝒜 hf g hg))) :
    ∃ ψ : Away 𝒜 (f * g) →+* B, ψ.comp (awayMap 𝒜 hg rfl) = φ := by
  let := (awayMap 𝒜 (f := f) hg rfl).toAlgebra
  have := Away.isLocalization_mul hf hg rfl (by decide : (1 : ℕ) ≠ 0)
  have hv : IsUnit (φ (Away.isLocalizationElem hf hg)) := by
    rw [isLocalizationElem_eq_normalized]
    exact hu
  exact ⟨IsLocalization.Away.lift (S := Away 𝒜 (f * g)) _ hv,
    IsLocalization.Away.lift_comp _ hv⟩

end GradedChart
end AllCharacteristics

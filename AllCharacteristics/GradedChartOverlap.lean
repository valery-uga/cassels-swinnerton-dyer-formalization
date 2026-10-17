import AllCharacteristics.GradedChartCoordinates

/-!
# Coordinate ratios on intersections of homogeneous charts

The actual homogeneous-localization maps to the product chart obey the
normalized-coordinate transition law. The two distinguished ratios are mutual
inverses, giving the unit needed to compare normalized universal equations.
-/

open HomogeneousLocalization
namespace AllCharacteristics
namespace GradedChart
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]
variable {f g x : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)

/-- A normalized coordinate maps to its numerator times the other chart
coordinate, divided by the product coordinate. -/
theorem val_awayMap_normalized (hx : x = f * g) (a : A) (ha : a ∈ 𝒜 1) :
    (awayMap 𝒜 hg hx (normalized 𝒜 hf a ha)).val =
      (Localization.mk (a * g) ⟨x, Submonoid.mem_powers x⟩ : Localization (.powers x)) := by
  simp only [normalized, awayMap_mk, Away.val_mk, pow_one]

/-- On the intersection of two charts, a/f = (g/f)(a/g). -/
theorem normalized_overlap_mul (a : A) (ha : a ∈ 𝒜 1) :
    awayMap 𝒜 hg rfl (normalized 𝒜 hf g hg) *
      awayMap 𝒜 hf (mul_comm f g) (normalized 𝒜 hg a ha) =
    awayMap 𝒜 hg rfl (normalized 𝒜 hf a ha) := by
  apply val_injective
  simp only [val_mul, val_awayMap_normalized, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

/-- The two distinguished ratios on a chart intersection are mutual inverses. -/
theorem normalized_overlap_inv :
    awayMap 𝒜 hg rfl (normalized 𝒜 hf g hg) *
      awayMap 𝒜 hf (mul_comm f g) (normalized 𝒜 hg f hf) = 1 := by
  rw [normalized_overlap_mul, normalized_self, map_one]

/-- The distinguished coefficient ratio as an actual unit in the overlap ring. -/
noncomputable def overlapCoordinateUnit : (Away 𝒜 (f * g))ˣ where
  val := awayMap 𝒜 hf (mul_comm f g) (normalized 𝒜 hg f hf)
  inv := awayMap 𝒜 hg rfl (normalized 𝒜 hf g hg)
  val_inv := (mul_comm _ _).trans (normalized_overlap_inv 𝒜 hf hg)
  inv_val := normalized_overlap_inv 𝒜 hf hg

/-- The value of the overlap unit is the first coordinate divided by the second. -/
theorem overlapCoordinateUnit_val :
    (overlapCoordinateUnit 𝒜 hf hg : Away 𝒜 (f * g)) =
      awayMap 𝒜 hf (mul_comm f g) (normalized 𝒜 hg f hf) := rfl

/-- Its inverse is the second coordinate divided by the first. -/
theorem overlapCoordinateUnit_inv :
    (↑((overlapCoordinateUnit 𝒜 hf hg)⁻¹) : Away 𝒜 (f * g)) =
      awayMap 𝒜 hg rfl (normalized 𝒜 hf g hg) := rfl

/-- Restriction to a product chart preserves the original base coefficients. -/
theorem awayMap_baseMap (hx : x = f * g) (r : R) :
    awayMap 𝒜 hg hx (baseMap 𝒜 (z := f) r) = baseMap 𝒜 (z := x) r :=
  awayMap_fromZeroRingHom 𝒜 hg hx (algebraMap R (𝒜 0) r)

end GradedChart
end AllCharacteristics

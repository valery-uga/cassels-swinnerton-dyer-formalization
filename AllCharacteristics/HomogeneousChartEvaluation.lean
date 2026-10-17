import AllCharacteristics.GradedChartCoordinates

/-!
# Evaluating a homogeneous chart at a coordinate equal to one

A ring homomorphism sending the distinguished coordinate to one extends to the
homogeneous chart. Every homogeneous fraction then evaluates to its numerator.
-/

open HomogeneousLocalization
namespace AllCharacteristics
namespace GradedChart
universe u v w
variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] (z : A)

/-- Evaluate a homogeneous chart when the distinguished coordinate maps to one. -/
noncomputable def liftCoordinateOne (e : A →+* B) (he : e z = 1) : Away 𝒜 z →+* B :=
  (IsLocalization.Away.lift z (he.symm ▸ isUnit_one) : Localization (.powers z) →+* B).comp
    (algebraMap (Away 𝒜 z) (Localization (.powers z)))

/-- A homogeneous fraction evaluates to its numerator if its denominator
coordinate maps to one. -/
theorem liftCoordinateOne_mk (e : A →+* B) (he : e z = 1) {d : ℕ}
    (hz : z ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    liftCoordinateOne 𝒜 z e he (Away.mk 𝒜 hz n a ha) = e a := by
  let L := Localization (.powers z)
  let l : L →+* B := IsLocalization.Away.lift z (he.symm ▸ isUnit_one)
  have h := congrArg l (IsLocalization.mk'_spec L a
    (⟨z ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers z))
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq,
    map_pow, he, one_pow, mul_one] at h
  change l (Localization.mk a ⟨z ^ n, ⟨n, rfl⟩⟩) = e a
  rw [Localization.mk_eq_mk']
  exact h

/-- Evaluation of a homogeneous chart preserves the original coefficient map. -/
theorem liftCoordinateOne_baseMap (e : A →+* B) (he : e z = 1) (r : R) :
    liftCoordinateOne 𝒜 z e he (baseMap 𝒜 (z := z) r) = e (algebraMap R A r) := by
  change IsLocalization.Away.lift z (he.symm ▸ isUnit_one)
    ((baseMap 𝒜 (z := z) r).val) = _
  rw [val_baseMap, IsLocalization.Away.lift_eq]

/-- A normalized coordinate evaluates to the image of its numerator. -/
theorem liftCoordinateOne_normalized (e : A →+* B) (he : e z = 1)
    (hz : z ∈ 𝒜 1) (a : A) (ha : a ∈ 𝒜 1) :
    liftCoordinateOne 𝒜 z e he (normalized 𝒜 hz a ha) = e a :=
  liftCoordinateOne_mk 𝒜 z e he hz 1 a (by simpa only [one_smul] using ha)

end GradedChart
end AllCharacteristics

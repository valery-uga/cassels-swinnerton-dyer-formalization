import AllCharacteristics.GradedChartCoordinates

/-! SOURCE ONLY / UNVERIFIED. Evaluation of the actual homogeneous
localization when the denominator evaluates to a unit. No chosen linear
coordinate or infinite-field hypothesis is needed. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.UnitChart004
open HomogeneousLocalization
open AllCharacteristics
universe u v w
variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] (z : A)

/-- The actual homogeneous chart embeds in ordinary localization, whose
universal property evaluates any unit-valued homogeneous denominator. -/
def liftUnit (e : A →+* B) (he : IsUnit (e z)) : Away 𝒜 z →+* B :=
  (IsLocalization.Away.lift z he : Localization (.powers z) →+* B).comp
    (algebraMap (Away 𝒜 z) (Localization (.powers z)))

/-- This exact multiplication identity evaluates every homogeneous fraction,
without introducing a fraction field or a normalization certificate. -/
theorem liftUnit_mk_mul (e : A →+* B) (he : IsUnit (e z)) {d : ℕ}
    (hz : z ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    liftUnit 𝒜 z e he (Away.mk 𝒜 hz n a ha) * (e z) ^ n = e a := by
  let L := Localization (.powers z)
  let l : L →+* B := IsLocalization.Away.lift z he
  have h := congrArg l (IsLocalization.mk'_spec L a
    (⟨z ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers z))
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq,
    map_pow] at h
  change l (Localization.mk a ⟨z ^ n, ⟨n, rfl⟩⟩) * (e z) ^ n = e a
  rw [Localization.mk_eq_mk']
  exact h

/-- Evaluation on the chart retains the original coefficient map. -/
theorem liftUnit_baseMap (e : A →+* B) (he : IsUnit (e z)) (r : R) :
    liftUnit 𝒜 z e he (GradedChart.baseMap 𝒜 (z := z) r) =
      e (algebraMap R A r) := by
  change IsLocalization.Away.lift z he
    ((GradedChart.baseMap 𝒜 (z := z) r).val) = _
  rw [GradedChart.val_baseMap, IsLocalization.Away.lift_eq]

/-- For the canonical original coordinate-ring inclusion into ordinary
localization, chart evaluation is exactly the original homogeneous-chart
inclusion. This supplies the identity side of coordinate reconstruction. -/
theorem liftUnit_algebraMap :
    liftUnit 𝒜 z (algebraMap A (Localization (.powers z)))
      (IsLocalization.Away.algebraMap_isUnit z) =
      algebraMap (Away 𝒜 z) (Localization (.powers z)) := by
  let L := Localization (.powers z)
  have h : (IsLocalization.Away.lift z
      (IsLocalization.Away.algebraMap_isUnit z) : L →+* L) = RingHom.id L := by
    apply IsLocalization.ringHom_ext (Submonoid.powers z)
    apply RingHom.ext
    intro a
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.Away.lift_eq,
      RingHom.id_apply]
  unfold liftUnit
  rw [h, RingHom.id_comp]

end PfaffianDescent.QuadraticSkewRationality.UnitChart004

import AllCharacteristics.HomogeneousSpecialization
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Normalized coordinates in a graded affine chart

Ratios of degree-one elements to the chart coordinate satisfy every homogeneous
relation satisfied by the original elements. This is proved inside the actual
degree-zero localization, without a field or characteristic assumption.
-/

open HomogeneousLocalization
namespace AllCharacteristics
namespace GradedChart
universe u v w
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] {z : A} (hz : z ∈ 𝒜 1)

/-- A degree-one element divided by the chart coordinate. -/
noncomputable def normalized (a : A) (ha : a ∈ 𝒜 1) : Away 𝒜 z :=
  Away.mk 𝒜 hz 1 a (by simpa only [one_smul] using ha)

/-- The coefficient homomorphism into the homogeneous chart ring. -/
noncomputable def baseMap : R →+* Away 𝒜 z :=
  (fromZeroRingHom 𝒜 (.powers z)).comp (algebraMap R (𝒜 0))

/-- In the ordinary localization, a normalized coordinate is multiplication by
the reciprocal of the chart coordinate. -/
theorem val_normalized (a : A) (ha : a ∈ 𝒜 1) :
    (normalized 𝒜 hz a ha).val =
      (Localization.mk 1 ⟨z, Submonoid.mem_powers z⟩ : Localization (.powers z)) *
        algebraMap A (Localization (.powers z)) a := by
  simp only [normalized, Away.val_mk, pow_one, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul, mul_one]

/-- Normalizing the chart coordinate itself gives one. -/
theorem normalized_self : normalized 𝒜 hz z hz = 1 := by
  apply val_injective
  simp only [normalized, Away.val_mk, pow_one, val_one]
  exact Localization.mk_self ⟨z, Submonoid.mem_powers z⟩

/-- The coefficient map agrees with the ordinary localization coefficient map. -/
theorem val_baseMap (r : R) :
    (baseMap 𝒜 (z := z) r).val =
      algebraMap A (Localization (.powers z)) (algebraMap R A r) := rfl

/-- Homogeneous polynomial relations persist after normalization in a chart. -/
theorem eval₂_normalized_eq_zero {σ : Type w} (x : σ → A)
    (hx : ∀ i, x i ∈ 𝒜 1) (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) (he : p.eval₂ (algebraMap R A) x = 0) :
    p.eval₂ (baseMap 𝒜 (z := z)) (fun i ↦ normalized 𝒜 hz (x i) (hx i)) = 0 := by
  let L := Localization (.powers z)
  let v : Away 𝒜 z →+* L := algebraMap (Away 𝒜 z) L
  let a : R →+* L := (algebraMap A L).comp (algebraMap R A)
  let c : L := Localization.mk 1 ⟨z, Submonoid.mem_powers z⟩
  have hb : v.comp (baseMap 𝒜 (z := z)) = a := by
    ext r
    exact val_baseMap 𝒜 r
  have hxv : (fun i ↦ v (normalized 𝒜 hz (x i) (hx i))) =
      c • (fun i ↦ algebraMap A L (x i)) := by
    funext i
    exact val_normalized 𝒜 hz (x i) (hx i)
  apply (val_injective (.powers z))
  change v (p.eval₂ (baseMap 𝒜 (z := z)) _) = v 0
  rw [MvPolynomial.hom_eval₂, hb, hxv, eval₂_homogeneous_smul p hp, map_zero]
  have hzero : p.eval₂ a (fun i ↦ algebraMap A L (x i)) = 0 := by
    rw [← MvPolynomial.hom_eval₂ p (algebraMap R A) (algebraMap A L) x, he, map_zero]
  rw [hzero, mul_zero]

end GradedChart
end AllCharacteristics

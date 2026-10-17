import AllCharacteristics.ProjectivePointCoordinates

/-!
# Polynomial generators of the homogeneous coordinate charts

Evaluation at normalized degree-one coordinates sends a homogeneous polynomial
of degree n to its class divided by the chart coordinate to the n-th power.
Every element of the actual homogeneous chart has this form. These identities
supply an explicit affine presentation for comparing coefficient changes.
-/

open HomogeneousLocalization
namespace AllCharacteristics
universe u v w

namespace GradedChart

/-- In the ordinary localization, evaluating a homogeneous polynomial at
normalized coordinates divides its unnormalized value by the appropriate power
of the chart coordinate. -/
theorem val_eval₂_normalized
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] {z : A} (hz : z ∈ 𝒜 1)
    {σ : Type w} (x : σ → A) (hx : ∀ i, x i ∈ 𝒜 1)
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    (p.eval₂ (baseMap 𝒜 (z := z)) (fun i ↦ normalized 𝒜 hz (x i) (hx i))).val =
      (Localization.mk 1 ⟨z, Submonoid.mem_powers z⟩ : Localization (.powers z)) ^ d *
        algebraMap A (Localization (.powers z)) (p.eval₂ (algebraMap R A) x) := by
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
  change v (p.eval₂ (baseMap 𝒜 (z := z)) _) = c ^ d * _
  rw [MvPolynomial.hom_eval₂, hb, hxv, eval₂_homogeneous_smul p hp]
  rw [← MvPolynomial.hom_eval₂ p (algebraMap R A) (algebraMap A L) x]

end GradedChart
namespace HomogeneousProjective
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- The class of a homogeneous polynomial lies in its specified quotient grade. -/
theorem polynomial_class_mem_grading (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) : Ideal.Quotient.mk I.toIdeal p ∈ grading I d :=
  ⟨p, hp, rfl⟩

/-- A homogeneous polynomial of degree n evaluates on a coordinate chart to
its class divided by the n-th power of the distinguished coordinate. -/
theorem eval₂_chartCoordinate_eq_fraction
    (j : σ) (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    p.eval₂ (chartBaseMap I j) (chartCoordinate I j) =
      Away.mk (grading I) (coordinate_mem I j) d (Ideal.Quotient.mk I.toIdeal p)
        (by simpa using polynomial_class_mem_grading I p hp) := by
  apply val_injective
  refine (GradedChart.val_eval₂_normalized (grading I) (coordinate_mem I j)
    (coordinate I) (coordinate_mem I) p hp).trans ?_
  have he : p.eval₂ (algebraMap R (CoordinateRing I)) (coordinate I) =
      Ideal.Quotient.mk I.toIdeal p := (congrFun (MvPolynomial.mk_eq_eval₂ I.toIdeal) p).symm
  rw [he, Away.val_mk]
  simp only [Localization.mk_pow, one_pow, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul, mul_one]
  rfl

/-- Normalized coordinate evaluation generates the entire affine chart ring. -/
theorem eval₂_chartCoordinate_surjective (j : σ) :
    Function.Surjective (MvPolynomial.eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) := by
  intro x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading I) (coordinate_mem I j) x
  have ha' : a ∈ grading I n := by simpa using ha
  obtain ⟨p, hp, rfl⟩ := ha'
  exact ⟨p, eval₂_chartCoordinate_eq_fraction I j p hp⟩

end HomogeneousProjective
end AllCharacteristics

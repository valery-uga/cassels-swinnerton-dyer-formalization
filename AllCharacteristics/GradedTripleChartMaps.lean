import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Product-chart restriction identities for a general graded algebra

The last and outer pair product charts both restrict to the same ordered
triple-product chart. Proving these identities before instantiating the graded
algebra keeps their kernel terms small.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace AllCharacteristics
namespace GradedChart
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]
variable {a b c : A} (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1) (hc : c ∈ 𝒜 1)

/-- The last-pair restriction has the ordered triple-product chart as its projective image. -/
theorem lastPair_toProj :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 ha ((mul_assoc a b c).trans (mul_comm a (b * c))))) ≫
      Proj.awayι 𝒜 (b * c) (SetLike.mul_mem_graded hb hc) (by decide : 0 < 2) =
    Proj.awayι 𝒜 (a * b * c) (SetLike.mul_mem_graded (SetLike.mul_mem_graded ha hb) hc)
      (by decide : 0 < 3) :=
  Proj.SpecMap_awayMap_awayι 𝒜 (SetLike.mul_mem_graded hb hc) (by decide : 0 < 2) ha
    ((mul_assoc a b c).trans (mul_comm a (b * c)))

/-- The outer-pair restriction has that same ordered triple-product chart as its image. -/
theorem outerPair_toProj :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 hb (mul_right_comm a b c))) ≫
      Proj.awayι 𝒜 (a * c) (SetLike.mul_mem_graded ha hc) (by decide : 0 < 2) =
    Proj.awayι 𝒜 (a * b * c) (SetLike.mul_mem_graded (SetLike.mul_mem_graded ha hb) hc)
      (by decide : 0 < 3) :=
  Proj.SpecMap_awayMap_awayι 𝒜 (SetLike.mul_mem_graded ha hc) (by decide : 0 < 2) hb
    (mul_right_comm a b c)

end GradedChart
end AllCharacteristics

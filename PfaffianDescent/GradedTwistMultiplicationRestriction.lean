import PfaffianDescent.VoisinHypersurfaceTwist

/-! # Actual graded restriction commutes with twist multiplication -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {A B σ₀ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ₀ A] [AddSubgroupClass σ₀ A]
  [SetLike τ B] [AddSubgroupClass τ B]
variable (𝒢 : ℕ → σ₀) (ℋ : ℕ → τ) [GradedRing 𝒢] [GradedRing ℋ]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of an actual twist section commutes with multiplication
by a homogeneous form, including its image in the quotient grading. -/
theorem gradedRingHomTwistToPushforward_mulHomogeneous
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤ (HomogeneousIdeal.irrelevant 𝒢).map f)
    {d : ℕ} (s : 𝒢 d) (m : ℕ) :
    mulHomogeneous 𝒢 s m ≫ gradedRingHomTwistToPushforward 𝒢 ℋ f hf m =
    gradedRingHomTwistToPushforward 𝒢 ℋ f hf (m + d) ≫
      (Scheme.Modules.pushforward (Proj.map f hf)).map
        (mulHomogeneous ℋ ⟨f s, f.2 s.2⟩ m) := by
  ext U z
  apply Subtype.ext
  funext y
  change Localization.localRingHom
    (pointIdeal 𝒢 (Proj.map f hf y.1)) (pointIdeal ℋ y.1) f.toRingHom rfl
      (algebraMap A (Fiber 𝒢 (Proj.map f hf y.1)) (s : A) *
        z.1 ⟨Proj.map f hf y.1, y.2⟩) =
    algebraMap B (Fiber ℋ y.1) (f s : B) *
      Localization.localRingHom
        (pointIdeal 𝒢 (Proj.map f hf y.1)) (pointIdeal ℋ y.1) f.toRingHom rfl
        (z.1 ⟨Proj.map f hf y.1, y.2⟩)
  rw [map_mul]
  congr 1
  rw [← Localization.mk_one_eq_algebraMap, Localization.localRingHom_mk]
  rw [← Localization.mk_one_eq_algebraMap]
  congr 1
  apply Subtype.ext
  exact f.toRingHom.map_one

end PfaffianDescent.ProjectiveNegativeTwist

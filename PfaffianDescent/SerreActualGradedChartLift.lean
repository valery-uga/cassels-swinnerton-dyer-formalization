import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! A genuine lift to the inverse image of a projective chart. Its existence
follows from the actual commuting projective square, without a separate
invertibility or chart-factorization assumption. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
variable [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
variable (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
variable (F : 𝒜 →+*ᵍ ℬ)
variable (hF : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map F)
variable (z : A) (hz : z ∈ 𝒜 1)
variable {T : Scheme.{u}} (k : T ⟶ Proj ℬ) (l : T ⟶ Spec (.of (Away 𝒜 z)))
variable (h : k ≫ Proj.map F hF = l ≫ Proj.awayι 𝒜 z hz (by decide : 0 < 1))
include hF l h

theorem serreActualGradedChartLift_range :
    Set.range k ⊆ Set.range (Proj.awayι ℬ (F z) (F.map_mem hz) (by decide : 0 < 1)) := by
  rintro x ⟨y, rfl⟩
  change k y ∈ (Proj.awayι ℬ (F z) (F.map_mem hz) (by decide : 0 < 1)).opensRange
  rw [Proj.opensRange_awayι]
  have he : Proj.map F hF (k y) = Proj.awayι 𝒜 z hz (by decide : 0 < 1) (l y) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m y) h
  have hy : Proj.map F hF (k y) ∈
      (Proj.awayι 𝒜 z hz (by decide : 0 < 1)).opensRange := by
    exact ⟨l y, he.symm⟩
  rw [Proj.opensRange_awayι] at hy
  exact hy

def serreActualGradedChartLift : T ⟶ Spec (.of (Away ℬ (F z))) :=
  IsOpenImmersion.lift (Proj.awayι ℬ (F z) (F.map_mem hz) (by decide : 0 < 1)) k
    (serreActualGradedChartLift_range 𝒜 ℬ F hF z hz k l h)

@[reassoc]
theorem serreActualGradedChartLift_toProj :
    serreActualGradedChartLift 𝒜 ℬ F hF z hz k l h ≫
      Proj.awayι ℬ (F z) (F.map_mem hz) (by decide : 0 < 1) = k :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem serreActualGradedChartLift_toChart :
    serreActualGradedChartLift 𝒜 ℬ F hF z hz k l h ≫
      Spec.map (CommRingCat.ofHom (Away.map F z)) = l := by
  apply (cancel_mono (Proj.awayι 𝒜 z hz (by decide : 0 < 1))).mp
  rw [Category.assoc, ← Proj.awayι_comp_map F hF (by decide : 0 < 1) z hz,
    ← Category.assoc, serreActualGradedChartLift_toProj]
  exact h

end PfaffianDescent

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! The actual map to a homogeneous overlap from two compatible chart
maps. Both restrictions are the original chart maps. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (f g : A) (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
variable {T : Scheme.{u}}
variable (a : T ⟶ Spec (.of (Away 𝒜 f))) (b : T ⟶ Spec (.of (Away 𝒜 g)))
variable (h : a ≫ Proj.awayι 𝒜 f hf (by decide : 0 < 1) =
  b ≫ Proj.awayι 𝒜 g hg (by decide : 0 < 1))

def serreActualGradedOverlapChartMap : T ⟶ Spec (.of (Away 𝒜 (f * g))) :=
  pullback.lift a b h ≫
    (Proj.pullbackAwayιIso 𝒜 hf (by decide : 0 < 1) hg (by decide : 0 < 1) rfl).hom

@[reassoc]
theorem serreActualGradedOverlapChartMap_left :
    serreActualGradedOverlapChartMap 𝒜 f g hf hg a b h ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 hg rfl)) = a := by
  unfold serreActualGradedOverlapChartMap
  rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left, pullback.lift_fst]

@[reassoc]
theorem serreActualGradedOverlapChartMap_right :
    serreActualGradedOverlapChartMap 𝒜 f g hf hg a b h ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 hf (mul_comm f g))) = b := by
  unfold serreActualGradedOverlapChartMap
  rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right, pullback.lift_snd]

end PfaffianDescent

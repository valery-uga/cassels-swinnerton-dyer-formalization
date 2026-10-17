import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Finite frames obtained from the image of a linear map

This file packages a basis of the range of a finite-dimensional linear map,
its underlying frame in the codomain, and a compatible choice of lifts in the
domain.  Keeping this construction abstract prevents large geometric source
and target types from being unfolded during later elaboration.
-/

namespace PfaffianDescent

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

/-- A frame bundled with its linear-independence proof.  The bundle keeps
large specialized frame expressions opaque when they are passed to later
constructions. -/
structure IndependentFrame (K : Type u) [Field K]
    (ι : Type v) (M : Type w) [AddCommGroup M] [Module K M] where
  toFun : ι → M
  linearIndependent : LinearIndependent K toFun

/-- Independent source and target frames with coordinatewise compatibility
under a fixed linear map. -/
structure LinearMapPairedIndependentFrame
    (L : V →ₗ[K] W) (ι : Type*) where
  source : IndependentFrame K ι V
  target : IndependentFrame K ι W
  map_toFun : ∀ i, L (source.toFun i) = target.toFun i

/-- A canonical finite basis of the range of a linear map with
finite-dimensional domain. -/
noncomputable def linearMapImageBasis (L : V →ₗ[K] W) [Module.Finite K V] :
    Module.Basis (Fin (Module.finrank K (LinearMap.range L))) K
      (LinearMap.range L) := by
  letI : Module.Free K (LinearMap.range L) :=
    Module.Free.of_divisionRing K (LinearMap.range L)
  exact Module.finBasis K (LinearMap.range L)

theorem exists_fin_linearMapImageBasis (L : V →ₗ[K] W) [Module.Finite K V] :
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) K (LinearMap.range L)) :=
  ⟨Module.finrank K (LinearMap.range L), ⟨linearMapImageBasis L⟩⟩

/-- The range basis viewed as a frame in the codomain. -/
noncomputable def linearMapImageFrame
    (L : V →ₗ[K] W) {ι : Type*}
    (b : Module.Basis ι K (LinearMap.range L)) : ι → W :=
  fun i => (b i : W)

theorem linearMapImageFrame_linearIndependent
    (L : V →ₗ[K] W) {ι : Type*}
    (b : Module.Basis ι K (LinearMap.range L)) :
    LinearIndependent K (linearMapImageFrame L b) := by
  have hker : (LinearMap.range L).subtype.ker = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (LinearMap.range L).subtype_injective
  change LinearIndependent K ((LinearMap.range L).subtype ∘ b)
  exact b.linearIndependent.map' (LinearMap.range L).subtype hker

/-- Choose one preimage of each vector in a basis of the range. -/
noncomputable def linearMapImageLiftFrame
    (L : V →ₗ[K] W) {ι : Type*}
    (b : Module.Basis ι K (LinearMap.range L)) : ι → V :=
  fun i => Classical.choose (b i).property

@[simp] theorem linearMapImageLiftFrame_map
    (L : V →ₗ[K] W) {ι : Type*}
    (b : Module.Basis ι K (LinearMap.range L)) (i : ι) :
    L (linearMapImageLiftFrame L b i) = linearMapImageFrame L b i := by
  exact Classical.choose_spec (b i).property

theorem linearMapImageLiftFrame_linearIndependent
    (L : V →ₗ[K] W) {ι : Type*}
    (b : Module.Basis ι K (LinearMap.range L)) :
    LinearIndependent K (linearMapImageLiftFrame L b) := by
  apply LinearIndependent.of_comp L
  convert linearMapImageFrame_linearIndependent L b using 1
  funext i
  exact linearMapImageLiftFrame_map L b i

/-- The basis of the image, bundled as an independent codomain frame. -/
noncomputable def linearMapImageIndependentFrame
    (L : V →ₗ[K] W) {ι : Type*}
    (b : Module.Basis ι K (LinearMap.range L)) :
    IndependentFrame K ι W where
  toFun := linearMapImageFrame L b
  linearIndependent := linearMapImageFrame_linearIndependent L b

/-- Compatible lifts of the image basis, bundled as an independent domain
frame. -/
noncomputable def linearMapImageLiftIndependentFrame
    (L : V →ₗ[K] W) {ι : Type*}
    (b : Module.Basis ι K (LinearMap.range L)) :
    IndependentFrame K ι V where
  toFun := linearMapImageLiftFrame L b
  linearIndependent := linearMapImageLiftFrame_linearIndependent L b

/-- The image basis and compatible independent lifts, bundled together. -/
noncomputable def linearMapImagePairedIndependentFrame
    (L : V →ₗ[K] W) {ι : Type*}
    (b : Module.Basis ι K (LinearMap.range L)) :
    LinearMapPairedIndependentFrame L ι where
  source := linearMapImageLiftIndependentFrame L b
  target := linearMapImageIndependentFrame L b
  map_toFun := linearMapImageLiftFrame_map L b

/-- Linear independence is preserved when a submodule-valued frame is
viewed in the ambient module. -/
theorem linearIndependent_submodule_coe_general
    {M : Type w} [AddCommGroup M] [Module K M]
    (S : Submodule K M) {ι : Type*} (v : ι → S)
    (hv : LinearIndependent K v) :
    LinearIndependent K (fun i => (v i : M)) := by
  have hker : S.subtype.ker = ⊥ :=
    LinearMap.ker_eq_bot_of_injective S.subtype_injective
  change LinearIndependent K (S.subtype ∘ v)
  exact hv.map' S.subtype hker

/-- View an independent frame in a submodule as an independent frame in the
ambient module. -/
noncomputable def IndependentFrame.submoduleCoe
    {M : Type w} [AddCommGroup M] [Module K M]
    (S : Submodule K M) {ι : Type v} (v : IndependentFrame K ι S) :
    IndependentFrame K ι M where
  toFun i := v.toFun i
  linearIndependent := linearIndependent_submodule_coe_general S v.toFun v.linearIndependent

end PfaffianDescent

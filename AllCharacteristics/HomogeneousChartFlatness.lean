import AllCharacteristics.GradedChartCoordinates
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Localization

/-!
# Flat homogeneous chart rings over Dedekind domains

A homogeneous chart embeds in the ordinary localization of its graded ring.
If the graded ring is flat over a Dedekind domain, the localization is flat and
the chart is torsion-free, hence flat. The chart coefficient homomorphism is
kept explicit, so this applies to the actual projective structure morphism.
-/

open HomogeneousLocalization
namespace AllCharacteristics
universe u v

/-- A degree-zero homogeneous chart of a flat graded algebra over a Dedekind
domain is flat for its natural coefficient homomorphism. -/
theorem homogeneousAway_flat_of_flat
    {R : Type u} {A : Type v} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] [Module.Flat R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] (z : A) :
    letI := (GradedChart.baseMap 𝒜 (z := z)).toAlgebra
    Module.Flat R (Away 𝒜 z) := by
  let H := Away 𝒜 z
  let L := Localization (Submonoid.powers z)
  let := (GradedChart.baseMap 𝒜 (z := z)).toAlgebra
  have : Module.Flat R L := Module.Flat.trans R A L
  let v : H →ₐ[R] L :=
    { __ := algebraMap H L
      commutes' := fun r ↦ GradedChart.val_baseMap 𝒜 (z := z) r }
  have : Module.IsTorsionFree R H := Function.Injective.moduleIsTorsionFree v
    (val_injective (Submonoid.powers z)) (fun r x ↦ v.toLinearMap.map_smul r x)
  infer_instance

end AllCharacteristics

import PfaffianDescent.AmbientPointKoszulSheafExactness
import PfaffianDescent.AmbientPointKoszulAugmentedExactness
import PfaffianDescent.ExtAcyclicResolutionDegreeThree

/-! # Three-step resolution from the actual standard-point Koszul maps

The two interior differential pairs are already proved exact. The builder
below uses only exactness of the actual augmented final pair, and keeps
the original twists and actual point restriction as the resolution terms.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization MvPolynomial

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- Actual standard-point Koszul resolution, after identifying the actual
augmentation as the final cokernel. No interior exactness is assumed. -/
def ambientPointKoszul_resolutionOfAugmentationExact
    (hzero : pointGlobalTraceP3CoordinateKoszulLast K ≫ ambientPointKoszul_augmentation K = 0)
    (hex : (ShortComplex.mk (pointGlobalTraceP3CoordinateKoszulLast K)
      (ambientPointKoszul_augmentation K) hzero).Exact) :
    ThreeStepResolution (Proj PS).Modules := by
  let d₀ := ambientPointKoszul_augmentation K
  let d₁ := pointGlobalTraceP3CoordinateKoszulLast K
  let d₂ := pointGlobalTraceP3CoordinateKoszulMiddle K
  let d₃ := pointGlobalTraceP3CoordinateKoszulFirst K
  let p₁ := kernel.lift d₀ d₁ hzero
  let p₂ := kernel.lift d₁ d₂ (pointGlobalTraceP3CoordinateKoszul_middle_last_zero K)
  have z₁ : kernel.ι d₁ ≫ p₁ = 0 := by
    apply (cancel_mono (kernel.ι d₀)).mp
    simp only [Category.assoc, p₁, kernel.lift_ι, kernel.condition, zero_comp]
  have z₂ : d₃ ≫ p₂ = 0 := by
    apply (cancel_mono (kernel.ι d₁)).mp
    simp only [Category.assoc, p₂, kernel.lift_ι,
      pointGlobalTraceP3CoordinateKoszul_first_middle_zero, zero_comp, d₃, d₂]
  let S₁ := ShortComplex.mk (kernel.ι d₁) p₁ z₁
  let S₂ := ShortComplex.mk d₃ p₂ z₂
  haveI : Epi d₀ := ambientPointKoszul_augmentation_epi K
  haveI : Epi p₁ := hex.epi_kernelLift
  haveI : Epi p₂ := (ambientPointKoszul_middleLast_exact K).epi_kernelLift
  haveI : Mono d₃ := ambientPointKoszul_first_mono K
  have he₁ : S₁.Exact := by
    let φ : S₁ ⟶ ShortComplex.kernelSequence d₁ :=
      ShortComplex.homMk (𝟙 _) (𝟙 _) (kernel.ι d₀)
        (by simp [S₁, ShortComplex.kernelSequence])
        (by simp [S₁, ShortComplex.kernelSequence, p₁])
    haveI : Epi φ.τ₁ := by change Epi (𝟙 (kernel d₁)); infer_instance
    haveI : IsIso φ.τ₂ := by change IsIso (𝟙 (⨁ pointGlobalTraceP3CoordinateTriple K 1)); infer_instance
    haveI : Mono φ.τ₃ := by change Mono (kernel.ι d₀); infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
      (ShortComplex.kernelSequence_exact d₁)
  have he₂ : S₂.Exact := by
    let φ : S₂ ⟶ ambientPointKoszul_firstMiddleShortComplex K :=
      ShortComplex.homMk (𝟙 _) (𝟙 _) (kernel.ι d₁)
        (by simp [S₂, ambientPointKoszul_firstMiddleShortComplex, d₃])
        (by simp [S₂, ambientPointKoszul_firstMiddleShortComplex, p₂, d₂])
    haveI : Epi φ.τ₁ := by change Epi (𝟙 (sheafOfModules PS 3)); infer_instance
    haveI : IsIso φ.τ₂ := by change IsIso (𝟙 (⨁ pointGlobalTraceP3CoordinateTriple K 2)); infer_instance
    haveI : Mono φ.τ₃ := by change Mono (kernel.ι d₁); infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
      (ambientPointKoszul_firstMiddle_exact K)
  exact
    { P := ambientPointKoszul_pointModule K
      C₀ := SheafOfModules.unit (Proj PS).ringCatSheaf
      C₁ := ⨁ pointGlobalTraceP3CoordinateTriple K 1
      C₂ := ⨁ pointGlobalTraceP3CoordinateTriple K 2
      K₀ := kernel d₀
      K₁ := kernel d₁
      K₂ := sheafOfModules PS 3
      i₀ := kernel.ι d₀
      p₀ := d₀
      zero₀ := kernel.condition d₀
      i₁ := kernel.ι d₁
      p₁ := p₁
      zero₁ := z₁
      i₂ := d₃
      p₂ := p₂
      zero₂ := z₂
      exact₀ :=
        { exact := ShortComplex.kernelSequence_exact d₀
          mono_f := by change Mono (kernel.ι d₀); infer_instance
          epi_g := by change Epi d₀; infer_instance }
      exact₁ :=
        { exact := he₁
          mono_f := by change Mono (kernel.ι d₁); infer_instance
          epi_g := by change Epi p₁; infer_instance }
      exact₂ :=
        { exact := he₂
          mono_f := by change Mono d₃; infer_instance
          epi_g := by change Epi p₂; infer_instance } }

/-- The resulting resolution's augmentation is the actual closed-immersion
unit restriction. -/
theorem ambientPointKoszul_resolutionOfAugmentationExact_p₀
    (hzero : pointGlobalTraceP3CoordinateKoszulLast K ≫ ambientPointKoszul_augmentation K = 0)
    (hex : (ShortComplex.mk (pointGlobalTraceP3CoordinateKoszulLast K)
      (ambientPointKoszul_augmentation K) hzero).Exact) :
    (ambientPointKoszul_resolutionOfAugmentationExact K hzero hex).p₀ =
      ambientPointKoszul_augmentation K := rfl

/-- The actual three-step Koszul resolution of the standard rational point
of projective three-space. All exactness and closed-immersion augmentation
comparisons have been proved. -/
def ambientPointKoszul_resolution : ThreeStepResolution (Proj PS).Modules :=
  ambientPointKoszul_resolutionOfAugmentationExact K
    (ambientPointKoszul_last_augmentation_zero K) (ambientPointKoszul_lastAugmentation_exact K)

@[simp]
theorem ambientPointKoszul_resolution_p₀ :
    (ambientPointKoszul_resolution K).p₀ = ambientPointKoszul_augmentation K := rfl

@[simp]
theorem ambientPointKoszul_resolution_C₀ :
    (ambientPointKoszul_resolution K).C₀ = SheafOfModules.unit (Proj PS).ringCatSheaf := rfl

@[simp]
theorem ambientPointKoszul_resolution_C₁ :
    (ambientPointKoszul_resolution K).C₁ = ⨁ pointGlobalTraceP3CoordinateTriple K 1 := rfl

@[simp]
theorem ambientPointKoszul_resolution_C₂ :
    (ambientPointKoszul_resolution K).C₂ = ⨁ pointGlobalTraceP3CoordinateTriple K 2 := rfl

@[simp]
theorem ambientPointKoszul_resolution_K₂ :
    (ambientPointKoszul_resolution K).K₂ = sheafOfModules PS 3 := rfl

@[simp]
theorem ambientPointKoszul_resolution_P :
    (ambientPointKoszul_resolution K).P = ambientPointKoszul_pointModule K := rfl

end PfaffianDescent.ProjectiveNegativeTwist

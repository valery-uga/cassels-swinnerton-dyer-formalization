import PfaffianDescent.PointGlobalTraceP3BasisKoszul
import PfaffianDescent.ExtAcyclicResolutionDegreeThree

/-! # Native resolution assembly for arbitrary degree-one point equations

The geometric exactness inputs are explicit. The construction preserves
the original native projective twist terms and the literal augmentation.
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
/-- Assemble the native three-step resolution from actual degree-one
Koszul maps and their proved geometric exactness. The augmentation is
retained literally as the specified sheaf morphism. -/
def pointGlobalTraceP3BasisResolution
    (f : Fin 4 → homogeneousSubmodule (Fin 4) K 1)
    (P : (Proj PS).Modules)
    (a : SheafOfModules.unit (Proj PS).ringCatSheaf ⟶ P) [Epi a]
    [Mono (pointGlobalTraceP3BasisKoszulFirst K f)]
    (hfirst : (ShortComplex.mk (pointGlobalTraceP3BasisKoszulFirst K f)
      (pointGlobalTraceP3BasisKoszulMiddle K f)
      (pointGlobalTraceP3BasisKoszul_first_middle_zero K f)).Exact)
    (hmiddle : (ShortComplex.mk (pointGlobalTraceP3BasisKoszulMiddle K f)
      (pointGlobalTraceP3BasisKoszulLast K f)
      (pointGlobalTraceP3BasisKoszul_middle_last_zero K f)).Exact)
    (hzero : pointGlobalTraceP3BasisKoszulLast K f ≫ a = 0)
    (hex : (ShortComplex.mk (pointGlobalTraceP3BasisKoszulLast K f) a hzero).Exact) :
    ThreeStepResolution (Proj PS).Modules := by
  let d₀ := a
  let d₁ := pointGlobalTraceP3BasisKoszulLast K f
  let d₂ := pointGlobalTraceP3BasisKoszulMiddle K f
  let d₃ := pointGlobalTraceP3BasisKoszulFirst K f
  let p₁ := kernel.lift d₀ d₁ hzero
  let p₂ := kernel.lift d₁ d₂ (pointGlobalTraceP3BasisKoszul_middle_last_zero K f)
  have z₁ : kernel.ι d₁ ≫ p₁ = 0 := by
    apply (cancel_mono (kernel.ι d₀)).mp
    simp only [Category.assoc, p₁, kernel.lift_ι, kernel.condition, zero_comp]
  have z₂ : d₃ ≫ p₂ = 0 := by
    apply (cancel_mono (kernel.ι d₁)).mp
    simp only [Category.assoc, p₂, kernel.lift_ι,
      pointGlobalTraceP3BasisKoszul_first_middle_zero, zero_comp, d₃, d₂]
  let S₁ := ShortComplex.mk (kernel.ι d₁) p₁ z₁
  let S₂ := ShortComplex.mk d₃ p₂ z₂
  haveI : Epi d₀ := inferInstance
  haveI : Epi p₁ := hex.epi_kernelLift
  haveI : Epi p₂ := hmiddle.epi_kernelLift
  haveI : Mono d₃ := inferInstance
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
    let φ : S₂ ⟶ ShortComplex.mk (pointGlobalTraceP3BasisKoszulFirst K f)
        (pointGlobalTraceP3BasisKoszulMiddle K f) (pointGlobalTraceP3BasisKoszul_first_middle_zero K f) :=
      ShortComplex.homMk (𝟙 _) (𝟙 _) (kernel.ι d₁)
        (by simp [S₂, ShortComplex.mk, d₃])
        (by simp [S₂, ShortComplex.mk, p₂, d₂])
    haveI : Epi φ.τ₁ := by change Epi (𝟙 (sheafOfModules PS 3)); infer_instance
    haveI : IsIso φ.τ₂ := by change IsIso (𝟙 (⨁ pointGlobalTraceP3CoordinateTriple K 2)); infer_instance
    haveI : Mono φ.τ₃ := by change Mono (kernel.ι d₁); infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
      hfirst
  exact
    { P := P
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

end PfaffianDescent.ProjectiveNegativeTwist

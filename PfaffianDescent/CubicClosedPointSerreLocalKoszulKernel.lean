import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # An exact Koszul row ending in the actual ideal kernel

A free coordinate on the augmented term, commuting with the actual
quotient, identifies the two kernels by universality. The resulting row
ends in the actual kernel object and remains short exact.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def cubicClosedPointSerreLocalKoszulKernelIso
    (B : ShortComplex C) (hB : B.ShortExact) : kernel B.g ≅ B.X₁ :=
  KernelFork.mapIsoOfIsLimit (kernelIsKernel B.g) hB.fIsKernel (Iso.refl (Arrow.mk B.g))

@[reassoc]
theorem cubicClosedPointSerreLocalKoszulKernelIso_hom_f
    (B : ShortComplex C) (hB : B.ShortExact) :
    (cubicClosedPointSerreLocalKoszulKernelIso B hB).hom ≫ B.f = kernel.ι B.g := by
  change (KernelFork.ofι (kernel.ι B.g) (kernel.condition B.g)).mapOfIsLimit
      hB.fIsKernel (𝟙 (Arrow.mk B.g)) ≫ B.f = kernel.ι B.g
  simpa using
    KernelFork.mapOfIsLimit_ι (KernelFork.ofι (kernel.ι B.g) (kernel.condition B.g))
      hB.fIsKernel (𝟙 (Arrow.mk B.g))

def cubicClosedPointSerreLocalKoszulToKernel
    (B : ShortComplex C) (hB : B.ShortExact) {C₀ C₁ : C}
    (e₀ : C₀ ≅ B.X₂) (d₁ : C₁ ⟶ C₀) (h₁₀ : (d₁ ≫ e₀.hom) ≫ B.g = 0) :
    C₁ ⟶ B.X₁ :=
  kernel.lift B.g (d₁ ≫ e₀.hom) h₁₀ ≫
    (cubicClosedPointSerreLocalKoszulKernelIso B hB).hom

@[reassoc]
theorem cubicClosedPointSerreLocalKoszulToKernel_f
    (B : ShortComplex C) (hB : B.ShortExact) {C₀ C₁ : C}
    (e₀ : C₀ ≅ B.X₂) (d₁ : C₁ ⟶ C₀) (h₁₀ : (d₁ ≫ e₀.hom) ≫ B.g = 0) :
    cubicClosedPointSerreLocalKoszulToKernel B hB e₀ d₁ h₁₀ ≫ B.f = d₁ ≫ e₀.hom := by
  simp only [cubicClosedPointSerreLocalKoszulToKernel, Category.assoc,
    cubicClosedPointSerreLocalKoszulKernelIso_hom_f, kernel.lift_ι]

theorem cubicClosedPointSerreLocalKoszulToKernel_epi
    (B : ShortComplex C) (hB : B.ShortExact) {C₀ C₁ : C}
    (e₀ : C₀ ≅ B.X₂) (d₁ : C₁ ⟶ C₀) (h₁₀ : (d₁ ≫ e₀.hom) ≫ B.g = 0)
    (hexact : (ShortComplex.mk (d₁ ≫ e₀.hom) B.g h₁₀).Exact) :
    Epi (cubicClosedPointSerreLocalKoszulToKernel B hB e₀ d₁ h₁₀) := by
  letI : Epi (kernel.lift B.g (d₁ ≫ e₀.hom) h₁₀) := hexact.epi_kernelLift
  dsimp [cubicClosedPointSerreLocalKoszulToKernel]
  infer_instance

def cubicClosedPointSerreLocalKoszulKernelComplex
    (B : ShortComplex C) (hB : B.ShortExact) {C₀ C₁ C₂ : C}
    (e₀ : C₀ ≅ B.X₂) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₁₀ : (d₁ ≫ e₀.hom) ≫ B.g = 0) (h₂₁ : d₂ ≫ d₁ = 0) : ShortComplex C :=
  ShortComplex.mk d₂ (cubicClosedPointSerreLocalKoszulToKernel B hB e₀ d₁ h₁₀) (by
    haveI : Mono B.f := hB.mono_f
    apply (cancel_mono B.f).mp
    simp only [Category.assoc, cubicClosedPointSerreLocalKoszulToKernel_f, zero_comp]
    simp only [← Category.assoc, h₂₁, zero_comp])

theorem cubicClosedPointSerreLocalKoszulKernelComplex_shortExact
    (B : ShortComplex C) (hB : B.ShortExact) {C₀ C₁ C₂ : C}
    (e₀ : C₀ ≅ B.X₂) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₁₀ : (d₁ ≫ e₀.hom) ≫ B.g = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₀ : (ShortComplex.mk (d₁ ≫ e₀.hom) B.g h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact) [Mono d₂] :
    (cubicClosedPointSerreLocalKoszulKernelComplex B hB e₀ d₁ d₂ h₁₀ h₂₁).ShortExact := by
  let S := cubicClosedPointSerreLocalKoszulKernelComplex B hB e₀ d₁ d₂ h₁₀ h₂₁
  haveI : Mono B.f := hB.mono_f
  let φ : S ⟶ ShortComplex.mk d₂ d₁ h₂₁ :=
    ShortComplex.homMk (𝟙 _) (𝟙 _) (B.f ≫ e₀.inv) (by
      change 𝟙 _ ≫ d₂ = d₂ ≫ 𝟙 _
      simp) (by
      simp only [S, cubicClosedPointSerreLocalKoszulKernelComplex, Category.id_comp,
        Category.assoc, cubicClosedPointSerreLocalKoszulToKernel_f_assoc,
        e₀.hom_inv_id, Category.comp_id])
  haveI : Epi φ.τ₁ := by change Epi (𝟙 C₂); infer_instance
  haveI : IsIso φ.τ₂ := by change IsIso (𝟙 C₁); infer_instance
  haveI : Mono φ.τ₃ := by change Mono (B.f ≫ e₀.inv); infer_instance
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hexact₁
  · change Mono d₂
    infer_instance
  · exact cubicClosedPointSerreLocalKoszulToKernel_epi B hB e₀ d₁ h₁₀ hexact₀

end PfaffianDescent

import AllCharacteristics.SchemeActionKernelPair
import AllCharacteristics.KernelPairBaseChange

/-! # ActionKernelPairBaseChange

The actual action-graph kernel-pair map commutes with Cartesian changes of an equivariant quotient. Both the commuting identity and the Cartesian square are proved for the original morphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v
variable {U X V Y : Scheme.{u}} (G : Type v) [Finite G] [Small.{u} G]
variable (τ : G → (U ⟶ U)) (ρ : G → (X ⟶ X))
variable {i : U ⟶ X} {r : U ⟶ V} {q : X ⟶ Y} {j : V ⟶ Y}
variable (h : IsPullback i r q j)
variable (hr : ∀ g, τ g ≫ r = r) (hq : ∀ g, ρ g ≫ q = q)
variable (heq : ∀ g, τ g ≫ i = i ≫ ρ g)

include heq in
lemma schemeActionKernelPairMap_baseChange_naturality :
    CategoryTheory.Limits.Sigma.map (f := fun _ : G => U) (g := fun _ : G => X) (fun _ => i) ≫
      schemeActionKernelPairMap G ρ q hq =
        schemeActionKernelPairMap G τ r hr ≫ kernelPairBaseChangeMap h := by
  apply Sigma.hom_ext
  intro g
  rw [← Category.assoc, Sigma.ι_map, Category.assoc]
  apply pullback.hom_ext
  · simp only [Category.assoc, kernelPairBaseChangeMap_fst]
    calc
      i ≫ Sigma.ι (fun _ : G => X) g ≫ schemeActionKernelPairMap G ρ q hq ≫ pullback.fst q q = i := by
        simpa only [Category.assoc, Category.comp_id] using
          congrArg (fun a => i ≫ a) (schemeActionKernelPairMap_component_fst G ρ q hq g)
      _ = Sigma.ι (fun _ : G => U) g ≫ schemeActionKernelPairMap G τ r hr ≫ pullback.fst r r ≫ i := by
        simpa only [Category.assoc, Category.id_comp] using
          (congrArg (fun a => a ≫ i) (schemeActionKernelPairMap_component_fst G τ r hr g)).symm
  · simp only [Category.assoc, kernelPairBaseChangeMap_snd]
    calc
      i ≫ Sigma.ι (fun _ : G => X) g ≫ schemeActionKernelPairMap G ρ q hq ≫ pullback.snd q q = i ≫ ρ g := by
        simpa only [Category.assoc] using
          congrArg (fun a => i ≫ a) (schemeActionKernelPairMap_component_snd G ρ q hq g)
      _ = τ g ≫ i := (heq g).symm
      _ = Sigma.ι (fun _ : G => U) g ≫ schemeActionKernelPairMap G τ r hr ≫ pullback.snd r r ≫ i := by
        simpa only [Category.assoc] using
          (congrArg (fun a => a ≫ i) (schemeActionKernelPairMap_component_snd G τ r hr g)).symm

include heq in
lemma isPullback_schemeActionKernelPairMap_baseChange :
    IsPullback
      (CategoryTheory.Limits.Sigma.map (f := fun _ : G => U) (g := fun _ : G => X) (fun _ => i))
      (schemeActionKernelPairMap G τ r hr) (schemeActionKernelPairMap G ρ q hq)
      (kernelPairBaseChangeMap h) := by
  have hs := isPullback_sigmaMap_constant (ι := G) i
  rw [← schemeActionKernelPairMap_fst G τ r hr, ← schemeActionKernelPairMap_fst G ρ q hq] at hs
  exact hs.of_bot (schemeActionKernelPairMap_baseChange_naturality G τ ρ h hr hq heq)
    (isPullback_kernelPairBaseChangeMap h)

end AllCharacteristics

import AllCharacteristics.SchemeActionKernelPair
import AllCharacteristics.KernelPairBaseChange
import AllCharacteristics.FlatImage

/-! # Image ideals under finite action quotients

When the actual action-graph map is an isomorphism onto the kernel pair, an equivariant affine morphism has its original kernel ideal recovered from its image by affine flat pullback. The source action only needs one identity component.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v

theorem isPullback_actionGraphs_of_kernelPair_isIso
    {X Y : Scheme.{u}} (G : Type v) [Finite G] [Small.{u} G]
    (ρ : G → (X ⟶ X)) (q : X ⟶ Y) (hq : ∀ g, ρ g ≫ q = q)
    [IsIso (schemeActionKernelPairMap G ρ q hq)] :
    IsPullback (Sigma.desc (fun _ : G => 𝟙 X)) (Sigma.desc ρ) q q := by
  have hc : Sigma.desc (fun _ : G => 𝟙 X) ≫ q = Sigma.desc ρ ≫ q := by
    apply Sigma.hom_ext
    intro g
    simp only [← Category.assoc, Sigma.ι_desc, Category.id_comp, hq]
  exact IsPullback.of_iso_pullback ⟨hc⟩ (asIso (schemeActionKernelPairMap G ρ q hq))
    (schemeActionKernelPairMap_fst G ρ q hq) (schemeActionKernelPairMap_snd G ρ q hq)

theorem kernel_comp_comap_of_actionKernelPair
    {D X Y : Scheme.{u}} (G : Type v) [Finite G] [Small.{u} G]
    (ρ : G → (X ⟶ X)) (q : X ⟶ Y) [IsAffineHom q] [Flat q]
    (hq : ∀ g, ρ g ≫ q = q) [IsIso (schemeActionKernelPairMap G ρ q hq)]
    (j : D ⟶ X) [IsAffineHom j] (γ : G → (D ⟶ D))
    (heq : ∀ g, γ g ≫ j = j ≫ ρ g) (g₀ : G) (h₀ : γ g₀ = 𝟙 D) :
    (j ≫ q).ker.comap q = j.ker := by
  let s := CategoryTheory.Limits.Sigma.map (f := fun _ : G => D) (g := fun _ : G => X) (fun _ => j)
  let c := Sigma.desc (fun _ : G => 𝟙 D)
  let a := Sigma.desc γ
  have hs : IsPullback s c (Sigma.desc (fun _ : G => 𝟙 X)) j := isPullback_sigmaMap_constant j
  have hg := isPullback_actionGraphs_of_kernelPair_isIso G ρ q hq
  have hp : IsPullback c (s ≫ Sigma.desc ρ) (j ≫ q) q := (hs.paste_horiz hg.flip).flip
  have he : s ≫ Sigma.desc ρ = a ≫ j := by
    apply Sigma.hom_ext
    intro g
    simp only [s, a, ← Category.assoc, Sigma.ι_map, Sigma.ι_desc]
    simpa only [Category.assoc, Sigma.ι_desc] using (heq g).symm
  have hk := kernel_of_affine_flat_baseChange hp
  rw [he] at hk
  rw [← hk]
  apply le_antisymm
  · have h := (Sigma.ι (fun _ : G => D) g₀).le_ker_comp (a ≫ j)
    have hc : Sigma.ι (fun _ : G => D) g₀ ≫ (a ≫ j) = j := by
      rw [← Category.assoc, show Sigma.ι (fun _ : G => D) g₀ ≫ a = γ g₀ from Sigma.ι_desc γ g₀,
        h₀, Category.id_comp]
    rwa [hc] at h
  · exact a.le_ker_comp j

end AllCharacteristics

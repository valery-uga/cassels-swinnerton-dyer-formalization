import AllCharacteristics.ActionKernelPairBaseChange
import AllCharacteristics.TargetOpenNeighborhoodCriterion
import AllCharacteristics.FreeQuotientChartFactorization
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Kernel pairs of free quotients from their actual affine charts

The original graph map is an isomorphism globally because its pullback to each invariant affine chart is the proved affine graph isomorphism. The open charts cover every point of the actual kernel pair.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X Y S : Scheme.{u}} (G : Type) [Group G] [Finite G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (q : X ⟶ Y) (hq : ∀ g, ρ g ≫ q = q)
variable (hOrbit : ∀ x y : X, q x = q y ↔ ∃ g : G, ρ g x = y)

include h₁ hcomp hOrbit in
theorem isIso_schemeActionKernelPairMap_of_freeQuotientCharts
    (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X) (g : G),
      g ≠ 1 → a ≫ ρ g ≠ a)
    (hcharts : ∀ x : X, ∃ (U : Scheme.{u}) (_ : IsAffine U)
      (τ : G → (U ⟶ U)) (hτ₁ : τ 1 = 𝟙 U)
      (hτcomp : ∀ g h : G, τ (g * h) = τ g ≫ τ h)
      (i : U ⟶ X) (_ : IsOpenImmersion i)
      (_hi : ∀ g : G, τ g ≫ i = i ≫ ρ g)
      (p : U ⟶ S) (hp : ∀ g : G, τ g ≫ p = p)
      (j : affineSchemeActionQuotient G τ hτ₁ hτcomp p hp ⟶ Y),
      IsOpenImmersion j ∧ x ∈ Set.range i ∧
        i ≫ q = affineSchemeActionQuotientMap G τ hτ₁ hτcomp p hp ≫ j) :
    IsIso (schemeActionKernelPairMap G ρ q hq) := by
  apply isIso_of_target_open_neighborhoods
  intro z
  obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hio, hi, p, hp, j, hjo, hx, hs⟩ :=
    hcharts (pullback.fst q q z)
  have : IsAffine U := hUa
  have : IsOpenImmersion i := hio
  have : IsOpenImmersion j := hjo
  let r := affineSchemeActionQuotientMap G τ hτ₁ hτcomp p hp
  have hr : ∀ g, τ g ≫ r = r := affineSchemeActionQuotientMap_invariant G τ hτ₁ hτcomp p hp
  have hstable := equivariant_opensRange_preimage G ρ h₁ hcomp τ i hi
  have hpb : IsPullback i r q j :=
    isPullback_orbitQuotient_openChart G ρ q hOrbit i j r hs hstable
  let k := kernelPairBaseChangeMap hpb
  have hK : IsPullback k (pullback.fst r r) (pullback.fst q q) i :=
    isPullback_kernelPairBaseChangeMap hpb
  have hko : IsOpenImmersion k :=
    MorphismProperty.of_isPullback hK.flip hio
  refine ⟨pullback r r, k, hko, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hx
    obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := pullback.fst q q) (g := i) z u hu.symm
    refine ⟨hK.isoPullback.inv w, ?_⟩
    exact (congrArg (fun a => a w) hK.isoPullback_inv_fst).trans hw
  · have hfU : ∀ (K : Type u) [Field K] (c : Spec (.of K) ⟶ U) (g : G),
        g ≠ 1 → c ≫ τ g ≠ c := by
      intro K _ c g hg he
      apply hfree K (c ≫ i) g hg
      rw [Category.assoc, ← hi, ← Category.assoc, he]
    have hMU : IsIso (schemeActionKernelPairMap G τ r hr) :=
      isIso_schemeActionKernelPairMap_affine_of_free G τ hτ₁ hτcomp p hp hfU
    have hM := isPullback_schemeActionKernelPairMap_baseChange G τ ρ hpb hr hq hi
    rw [← hM.isoPullback_inv_snd]
    infer_instance

end AllCharacteristics

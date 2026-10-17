import AllCharacteristics.FreeAffineSchemeFactorization
import AllCharacteristics.FlatFactorizationGluing
import AllCharacteristics.OrbitQuotientOpenCharts
import AllCharacteristics.EquivariantOpenImage

/-! # Descent of invariant morphisms through actual free affine quotient charts -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X Y S : Scheme.{u}} (G : Type) [Group G] [Finite G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (q : X ⟶ Y) [Flat q] [Surjective q]
variable (hOrbit : ∀ x y : X, q x = q y ↔ ∃ g : G, ρ g x = y)

include h₁ hcomp hOrbit in
/-- A flat orbit quotient covered by its actual free affine invariant-spectrum
charts has the categorical quotient property for arbitrary scheme targets. -/
theorem existsUnique_freeQuotientChartFactor
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
        i ≫ q = affineSchemeActionQuotientMap G τ hτ₁ hτcomp p hp ≫ j)
    {T : Scheme.{u}} (a : X ⟶ T) (ha : ∀ g : G, ρ g ≫ a = a) :
    ∃! b : Y ⟶ T, q ≫ b = a := by
  apply existsUnique_factor_of_flat_pullback_neighborhoods q a
  intro y
  obtain ⟨x, hxy⟩ := q.surjective y
  obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hio, hi, p, hp, j, hjo, hx, hs⟩ := hcharts x
  have : IsAffine U := hUa
  have : IsOpenImmersion i := hio
  have : IsOpenImmersion j := hjo
  let r := affineSchemeActionQuotientMap G τ hτ₁ hτcomp p hp
  have hstable := equivariant_opensRange_preimage G ρ h₁ hcomp τ i hi
  have hpb : IsPullback i r q j :=
    isPullback_orbitQuotient_openChart G ρ q hOrbit i j r hs hstable
  refine ⟨U, affineSchemeActionQuotient G τ hτ₁ hτcomp p hp, i, j, r, hjo, ?_, hpb, ?_⟩
  · obtain ⟨u, hu⟩ := hx
    refine ⟨r u, ?_⟩
    exact (congrArg (fun m : U ⟶ Y ↦ m u) hs).symm.trans
      ((congrArg q hu).trans hxy)
  · have hfU : ∀ (K : Type u) [Field K] (c : Spec (.of K) ⟶ U) (g : G),
        g ≠ 1 → c ≫ τ g ≠ c := by
      intro K _ c g hg he
      apply hfree K (c ≫ i) g hg
      rw [Category.assoc, ← hi, ← Category.assoc, he]
    have haU : ∀ g : G, τ g ≫ (i ≫ a) = i ≫ a := by
      intro g
      rw [← Category.assoc, hi, Category.assoc, ha]
    obtain ⟨b, hb, _⟩ := existsUnique_freeAffineSchemeActionFactor
      G τ hτ₁ hτcomp p hp hfU (i ≫ a) haU
    exact ⟨b, hb⟩

end AllCharacteristics

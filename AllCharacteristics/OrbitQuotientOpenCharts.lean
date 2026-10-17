import AllCharacteristics.SchemeOrbitQuotientOpens

/-!
# Actual pullback squares from invariant open quotient charts

The proved orbit fibers identify the full inverse image of an invariant chart.
Together with the open immersions this proves the scheme-theoretic pullback
square; no inference from equality of field-valued morphisms is used.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X Y U V : Scheme.{u}} (G : Type v) (ρ : G → (X ⟶ X)) (q : X ⟶ Y)
variable (hOrbit : ∀ x y : X, q x = q y ↔ ∃ g : G, ρ g x = y)
variable (i : U ⟶ X) [IsOpenImmersion i] (j : V ⟶ Y) [IsOpenImmersion j]
variable (r : U ⟶ V) [Surjective r] (hs : i ≫ q = r ≫ j)
variable (hstable : ∀ g : G, (ρ g) ⁻¹ᵁ i.opensRange = i.opensRange)

omit [IsOpenImmersion j] in
include hOrbit hs hstable in
/-- The whole inverse image of an invariant quotient chart is the original
invariant open chart, for the actual underlying scheme points. -/
theorem orbitQuotient_openChart_preimage_range :
    q ⁻¹' Set.range j = Set.range i := by
  ext x
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨u, hu⟩ := r.surjective v
    have hs' : q (i u) = j (r u) := congrArg (fun m : U ⟶ Y ↦ m u) hs
    have he : q x = q (i u) := hv.symm.trans ((congrArg j hu).symm.trans hs'.symm)
    obtain ⟨g, hg⟩ := (hOrbit x (i u)).mp he
    have hm : x ∈ (ρ g) ⁻¹ᵁ i.opensRange := ⟨u, hg.symm⟩
    rw [hstable] at hm
    exact hm
  · rintro ⟨u, rfl⟩
    exact ⟨r u, (congrArg (fun m : U ⟶ Y ↦ m u) hs).symm⟩

include hOrbit hs hstable in
/-- Invariant open charts give actual Cartesian quotient squares. -/
theorem isPullback_orbitQuotient_openChart : IsPullback i r q j := by
  apply (IsOpenImmersion.isPullback r i j q hs ?_).flip
  apply SetLike.coe_injective
  exact orbitQuotient_openChart_preimage_range G ρ q hOrbit i j r hs hstable

end AllCharacteristics

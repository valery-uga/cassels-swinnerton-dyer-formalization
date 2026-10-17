import AllCharacteristics.InvariantMapFunctoriality

/-!
# Restriction of equivariant ring isomorphisms to invariant rings

A bijective equivariant ring homomorphism induces a bijection of its actual
invariant rings. The inverse preserves invariants by injectivity of the
original map, so no averaging or condition on the group order is needed.
-/

namespace AllCharacteristics
universe u v
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : Type v) [Group G]
variable [MulSemiringAction G A] [MulSemiringAction G B]
variable [SMulCommClass G R A] [SMulCommClass G R B]
variable (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)

/-- A bijective equivariant ring map restricts to a bijection of its actual invariant rings. -/
theorem equivariantInvariantMap_bijective (hbij : Function.Bijective φ) :
    Function.Bijective (equivariantInvariantMap R A B G φ hφ) := by
  constructor
  · intro a a' h
    apply Subtype.ext
    apply hbij.injective
    exact congrArg Subtype.val h
  · intro b
    obtain ⟨a, ha⟩ := hbij.surjective b.val
    have hfixed (g : G) : g • a = a := by
      apply hbij.injective
      rw [hφ, ha, b.property g]
    refine ⟨⟨a, hfixed⟩, ?_⟩
    apply Subtype.ext
    exact ha

/-- The actual invariant-ring equivalence induced by a bijective equivariant ring map. -/
noncomputable def equivariantInvariantRingEquiv (hbij : Function.Bijective φ) :
    FixedPoints.subalgebra R A G ≃+* FixedPoints.subalgebra R B G :=
  RingEquiv.ofBijective (equivariantInvariantMap R A B G φ hφ)
    (equivariantInvariantMap_bijective R A B G φ hφ hbij)

/-- The invariant-ring equivalence retains the original induced invariant homomorphism. -/
theorem equivariantInvariantRingEquiv_toRingHom (hbij : Function.Bijective φ) :
    (equivariantInvariantRingEquiv R A B G φ hφ hbij).toRingHom =
      equivariantInvariantMap R A B G φ hφ := rfl

end AllCharacteristics

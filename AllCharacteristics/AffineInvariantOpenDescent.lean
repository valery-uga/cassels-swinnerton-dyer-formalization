import AllCharacteristics.AffineInvariantQuotient

/-!
# Descent of invariant opens to affine finite-group quotients

The image of a group-stable open is open in the actual invariant spectrum,
and its inverse image is precisely the original open. Consequently every
point in a stable open has an invariant principal neighborhood inside it.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Pointwise
namespace AllCharacteristics
universe u v
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (G : Type v) [Group G] [Finite G]
variable [MulSemiringAction G A] [SMulCommClass G R A]
variable (U : (Spec (.of A)).Opens)
variable (hU : ∀ (p q : PrimeSpectrum A) (g : G),
  q.asIdeal = g • p.asIdeal → p ∈ U → q ∈ U)

include hU in
/-- A stable open is the full inverse image of its image in the invariant spectrum. -/
theorem preimage_image_affineInvariantOpen :
    (affineInvariantQuotientMap R A G) ⁻¹'
      ((affineInvariantQuotientMap R A G) '' (U : Set (Spec (.of A)))) = U := by
  ext p
  constructor
  · rintro ⟨q, hq, he⟩
    obtain ⟨g, hg⟩ := (affineInvariantQuotientMap_eq_iff R A G q p).mp he
    exact hU q p g hg hq
  · intro hp
    exact ⟨p, hp, rfl⟩

include hU in
/-- The image of a stable open is open in the actual affine invariant quotient. -/
theorem isOpen_image_affineInvariantOpen :
    IsOpen ((affineInvariantQuotientMap R A G) '' (U : Set (Spec (.of A)))) := by
  apply (isQuotientMap_affineInvariantQuotientMap R A G).isCoinducing.isOpen_preimage.mp
  rw [preimage_image_affineInvariantOpen R A G U hU]
  exact U.isOpen

/-- The actual descended open of the invariant spectrum. -/
def affineInvariantQuotientOpen : (affineInvariantQuotient R A G).Opens :=
  ⟨(affineInvariantQuotientMap R A G) '' (U : Set (Spec (.of A))),
    isOpen_image_affineInvariantOpen R A G U hU⟩

/-- Pulling back the descended open recovers the original stable open exactly. -/
theorem affineInvariantQuotientOpen_preimage :
    (affineInvariantQuotientMap R A G) ⁻¹ᵁ affineInvariantQuotientOpen R A G U hU = U := by
  apply SetLike.coe_injective
  exact preimage_image_affineInvariantOpen R A G U hU

include hU in
/-- Stable opens admit a basis of principal opens defined by invariant elements. -/
theorem exists_invariant_basicOpen_inside (p : PrimeSpectrum A) (hp : p ∈ U) :
    ∃ t : FixedPoints.subalgebra R A G,
      p ∈ PrimeSpectrum.basicOpen t.val ∧ (PrimeSpectrum.basicOpen t.val : Set (PrimeSpectrum A)) ⊆ (U : Set (Spec (.of A))) := by
  let V := affineInvariantQuotientOpen R A G U hU
  have hq : affineInvariantQuotientMap R A G p ∈ V := ⟨p, hp, rfl⟩
  obtain ⟨_, ⟨t, rfl⟩, ht, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp V.isOpen
      (affineInvariantQuotientMap R A G p) hq
  refine ⟨t, ht, ?_⟩
  intro q hq
  have hmem : affineInvariantQuotientMap R A G q ∈ V := hsub hq
  have he := affineInvariantQuotientOpen_preimage R A G U hU
  change q ∈ (affineInvariantQuotientMap R A G) ⁻¹ᵁ V at hmem
  rw [he] at hmem
  exact hmem

end AllCharacteristics

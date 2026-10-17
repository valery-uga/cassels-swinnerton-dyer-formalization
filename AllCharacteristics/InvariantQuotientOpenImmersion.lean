import AllCharacteristics.InvariantOpenNeighborhoods
import AllCharacteristics.InvariantOpenLocalIsomorphism
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Equivariant affine open immersions descend to open immersions

The actual morphism of invariant spectra is injective by the orbit
comparison. Its principal open restrictions are the proved localized
invariant isomorphisms, so it is an open immersion over every base ring,
including when the group order is not invertible.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : Type v) [Group G] [Finite G]
variable [MulSemiringAction G A] [MulSemiringAction G B]
variable [SMulCommClass G R A] [SMulCommClass G R B]
variable (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)
variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))]

/-- Every equivariant affine open immersion induces an actual open immersion
of the invariant quotient schemes. -/
theorem isOpenImmersion_affineInvariantQuotientMorphism :
    IsOpenImmersion (affineInvariantQuotientMorphism R A B G φ hφ) := by
  apply IsOpenImmersion.of_forall_source_exists
  · exact affineInvariantQuotientMorphism_injective R A B G φ hφ
      (Spec.map (CommRingCat.ofHom φ)).isOpenEmbedding.injective
  · intro x
    obtain ⟨t, hxt, ht⟩ := exists_invariant_basicOpen_at_source_quotient R A B G φ hφ x
    let β := equivariantInvariantMap R A B G φ hφ
    let i : Spec (.of (Localization.Away (β t))) ⟶ affineInvariantQuotient R B G :=
      Spec.map (CommRingCat.ofHom
        (algebraMap (FixedPoints.subalgebra R B G) (Localization.Away (β t))))
    have hi : IsOpenImmersion i := inferInstanceAs (IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (algebraMap (FixedPoints.subalgebra R B G) (Localization.Away (β t))))))
    refine ⟨_, i, hi, ?_, ?_⟩
    · have hr := PrimeSpectrum.localization_away_comap_range (Localization.Away (β t)) (β t)
      exact (Set.ext_iff.mp hr x).mpr hxt
    · have : IsIso (Spec.map (CommRingCat.ofHom (Localization.awayMap β t))) :=
        isIso_Spec_localizedInvariantMap_of_basicOpen_subset R A B G φ hφ t ht
      change IsOpenImmersion
        (Spec.map (CommRingCat.ofHom
          (algebraMap (FixedPoints.subalgebra R B G) (Localization.Away (β t)))) ≫
            Spec.map (CommRingCat.ofHom β))
      rw [(isPullback_Spec_awayMap β t).w]
      infer_instance

end AllCharacteristics

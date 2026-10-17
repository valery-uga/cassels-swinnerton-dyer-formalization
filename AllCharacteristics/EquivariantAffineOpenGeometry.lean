import AllCharacteristics.InvariantMapFunctoriality
import AllCharacteristics.InvariantPrimeOrbits

/-!
# Geometry of equivariant affine maps and their invariant quotients

The actual spectrum maps commute with the group action. Their image is
stable under the ideal action, and an injective equivariant spectrum map
induces an injective map of invariant quotients. These statements connect
the orbit descriptions with the open-overlap localization comparisons.
-/

open AlgebraicGeometry CategoryTheory
open scoped Pointwise
namespace AllCharacteristics
universe u v
section SpectrumMaps
variable (A B : Type u) [CommRing A] [CommRing B]
variable (G : Type v) [Group G] [MulSemiringAction G A] [MulSemiringAction G B]
variable (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)

include hφ

/-- The actual spectrum morphism of an equivariant ring map commutes with the group maps. -/
theorem SpecMap_equivariant (g : G) :
    Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G B g)) ≫
      Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom φ) ≫
          Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun h : CommRingCat.of A ⟶ CommRingCat.of B ↦ Spec.map h)
  apply ConcreteCategory.hom_ext
  intro a
  exact (hφ g a).symm

/-- The image of an actual equivariant spectrum map is stable under the original ideal action. -/
theorem SpecMap_range_stable (p q : PrimeSpectrum A) (g : G)
    (hg : q.asIdeal = g • p.asIdeal) (hp : p ∈ Set.range (Spec.map (CommRingCat.ofHom φ))) :
    q ∈ Set.range (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨b, rfl⟩ := hp
  refine ⟨PrimeSpectrum.comap (MulSemiringAction.toRingHom G B g⁻¹) b, ?_⟩
  have hc := congrArg (fun h : Spec (.of B) ⟶ Spec (.of A) ↦ h b)
    (SpecMap_equivariant A B G φ hφ g⁻¹)
  have hq : PrimeSpectrum.comap (MulSemiringAction.toRingHom G A g⁻¹)
      (Spec.map (CommRingCat.ofHom φ) b) = q := by
    apply PrimeSpectrum.ext
    change (PrimeSpectrum.comap (MulSemiringAction.toRingHom G A g⁻¹)
      (PrimeSpectrum.comap φ b)).asIdeal = q.asIdeal
    rw [primeSpectrum_comap_smul_asIdeal, inv_inv]
    exact hg.symm
  exact hc.trans hq

end SpectrumMaps

/-- An injective equivariant spectrum map induces an injective map of actual invariant quotients. -/
theorem affineInvariantQuotientMorphism_injective
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (G : Type v) [Group G] [Finite G]
    [MulSemiringAction G A] [MulSemiringAction G B] [SMulCommClass G R A] [SMulCommClass G R B]
    (φ : A →+* B) (hφ : ∀ (g : G) (a : A), φ (g • a) = g • φ a)
    (hφinj : Function.Injective (Spec.map (CommRingCat.ofHom φ))) :
    Function.Injective (affineInvariantQuotientMorphism R A B G φ hφ) := by
  intro x y h
  obtain ⟨p, rfl⟩ := (affineInvariantQuotientMap R B G).surjective x
  obtain ⟨q, rfl⟩ := (affineInvariantQuotientMap R B G).surjective y
  have he (z : Spec (.of B)) :
      affineInvariantQuotientMorphism R A B G φ hφ (affineInvariantQuotientMap R B G z) =
        affineInvariantQuotientMap R A G (Spec.map (CommRingCat.ofHom φ) z) :=
    congrArg (fun m : Spec (.of B) ⟶ affineInvariantQuotient R A G ↦ m z)
      (affineInvariantQuotientMorphism_square R A B G φ hφ)
  rw [he, he] at h
  obtain ⟨g, hg⟩ := (affineInvariantQuotientMap_eq_iff_comap R A G
    (Spec.map (CommRingCat.ofHom φ) p) (Spec.map (CommRingCat.ofHom φ) q)).mp h
  apply (affineInvariantQuotientMap_eq_iff_comap R B G p q).mpr
  refine ⟨g, hφinj ?_⟩
  exact (congrArg (fun m : Spec (.of B) ⟶ Spec (.of A) ↦ m p)
    (SpecMap_equivariant A B G φ hφ g)).trans hg

end AllCharacteristics

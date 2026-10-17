import AllCharacteristics.AffineInvariantQuotient

/-!
# Prime-spectrum orbits of the actual ring action maps

The ideal action and the contravariant maps of prime spectra agree with the
correct inverse. Thus the fibers of the invariant quotient are precisely
orbits under the actual spectrum maps of the ring action.
-/

open AlgebraicGeometry CategoryTheory
open scoped Pointwise
namespace AllCharacteristics
universe u v

/-- Pulling back a prime by a group ring automorphism gives its inverse-translated ideal. -/
theorem primeSpectrum_comap_smul_asIdeal (A : Type u) [CommRing A]
    (G : Type v) [Group G] [MulSemiringAction G A] (g : G) (p : PrimeSpectrum A) :
    (PrimeSpectrum.comap (MulSemiringAction.toRingHom G A g) p).asIdeal = g⁻¹ • p.asIdeal := by
  apply Ideal.ext
  intro a
  change g • a ∈ p.asIdeal ↔ a ∈ g⁻¹ • p.asIdeal
  exact Ideal.mem_inv_pointwise_smul_iff.symm

/-- Invariant quotient fibers are exactly the orbits of the actual prime-spectrum action maps. -/
theorem affineInvariantQuotientMap_eq_iff_comap (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    (p q : PrimeSpectrum A) :
    affineInvariantQuotientMap R A G p = affineInvariantQuotientMap R A G q ↔
      ∃ g : G, PrimeSpectrum.comap (MulSemiringAction.toRingHom G A g) p = q := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (affineInvariantQuotientMap_eq_iff R A G p q).mp h
    refine ⟨g⁻¹, ?_⟩
    apply PrimeSpectrum.ext
    rw [primeSpectrum_comap_smul_asIdeal, inv_inv]
    exact hg.symm
  · rintro ⟨g, rfl⟩
    apply (affineInvariantQuotientMap_eq_iff R A G p _).mpr
    exact ⟨g⁻¹, primeSpectrum_comap_smul_asIdeal A G g p⟩

end AllCharacteristics

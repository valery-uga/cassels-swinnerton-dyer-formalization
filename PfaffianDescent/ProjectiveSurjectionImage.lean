import PfaffianDescent.ProjectiveClosedImmersion

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)

/-- The image of the closed projective embedding induced by a graded
surjection is precisely the projective zero locus of its kernel. -/
theorem projectiveMap_mem_range_iff
    (x : Proj 𝒜) :
    x ∈ Set.range (Proj.map f (gradedSurjective_irrelevant_le f hf)) ↔
      RingHom.ker f.toRingHom ≤ x.asHomogeneousIdeal.toIdeal := by
  constructor
  · rintro ⟨y, rfl⟩ a ha
    change f a ∈ y.asHomogeneousIdeal
    change f a = 0 at ha
    rw [ha]
    exact Ideal.zero_mem _
  · intro hx
    have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    let P := x.asHomogeneousIdeal.map f
    have hback : P.toIdeal.comap f = x.asHomogeneousIdeal.toIdeal := by
      change (x.asHomogeneousIdeal.toIdeal.map f).comap f = _
      rw [Ideal.comap_map_of_surjective f hf, sup_eq_left]
      exact hx
    obtain ⟨Q, hQ, hQc⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime
      (f := f.toRingHom) x.asHomogeneousIdeal.toIdeal).mp hback
    have heQ : P.toIdeal = Q := by
      change x.asHomogeneousIdeal.toIdeal.map f = Q
      rw [← hQc]
      exact Ideal.map_comap_of_surjective f.toRingHom hf Q
    have hp : P.toIdeal.IsPrime := heQ.symm ▸ hQ
    have hback' : P.comap f = x.asHomogeneousIdeal := HomogeneousIdeal.ext hback
    have hnot : ¬ HomogeneousIdeal.irrelevant ℬ ≤ P := by
      intro h
      apply x.not_irrelevant_le
      apply (HomogeneousIdeal.irrelevant_le 𝒜).mpr
      intro n hn a ha
      have hm : f a ∈ P := h (HomogeneousIdeal.mem_irrelevant_of_mem ℬ hn (f.2 ha))
      change a ∈ P.comap f at hm
      rwa [hback'] at hm
    refine ⟨⟨P, hp, hnot⟩, ?_⟩
    apply ProjectiveSpectrum.ext
    exact hback'

end
end PfaffianDescent

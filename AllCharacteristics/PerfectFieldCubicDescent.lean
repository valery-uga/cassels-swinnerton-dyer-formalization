import AllCharacteristics.WittLiftingBase
import AllCharacteristics.DVRSourceCubicDescent

/-!
# Mixed-characteristic cubic descent over perfect residue fields

For a perfect field of positive characteristic, the Witt lifting base is
constructed within the proof. A nonzero smooth cubic with an effective cycle
of degree four or five therefore has a rational point. The signed degree-one
reduction is not assumed here; it remains a separate geometric obligation.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective
universe u
variable {k : Type u} [Field k]

/-- A smooth cubic over a perfect field of positive characteristic with an
effective cycle of degree four or five has a rational coordinate point. -/
theorem cubic_coordinates_of_effective_degree_four_or_five_perfect_positive
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  have := wittVector_charZero ℓ k
  have := wittVector_isAdicComplete_maximalIdeal ℓ k
  exact cubic_coordinates_of_effective_degree_four_or_five_over_DVR_residue
    (K := FractionRing (WittVector ℓ k)) WittVector.constantCoeff
    (WittVector.constantCoeff_surjective ℓ) p hp hne z hz

/-- The rational point produced by mixed-characteristic descent is an actual
section of the cubic surface's structure morphism. -/
theorem cubic_section_of_effective_degree_four_or_five_perfect_positive
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp, a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨y, hy, he⟩ := cubic_coordinates_of_effective_degree_four_or_five_perfect_positive
    ℓ p hp hne z hz
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy he
  exact ⟨a, by simpa using ha⟩

/-- Closed points of degree four or five suffice over every perfect field of
positive characteristic, with the lifting base constructed in the proof. -/
theorem cubic_section_of_closedPoint_degree_four_or_five_perfect_positive
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 5) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp, a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  apply cubic_section_of_effective_degree_four_or_five_perfect_positive ℓ p hp hne
    (Finsupp.single x 1)
  simpa [EffectiveZeroCycle.degree] using hx

end AllCharacteristics

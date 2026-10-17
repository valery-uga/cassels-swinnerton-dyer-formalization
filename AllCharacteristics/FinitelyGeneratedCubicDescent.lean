import AllCharacteristics.FinitelyGeneratedDVRLifting
import AllCharacteristics.DVRSourceCubicDescent

/-!
# Cubic degree-four/five descent over finitely generated imperfect fields

For a finitely generated field of positive characteristic, the complete DVR
lifting base is constructed by lifting its prime field, a transcendence basis,
and the remaining finite extension. The smooth cubic and its effective cycle
then lift by the proved source-cycle construction. Characteristic-zero descent
and proper specialization give a rational point over the original field.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective
universe u
variable {k : Type u} [Field k]

/-- A smooth cubic over a finitely generated field of positive characteristic
with an effective cycle of degree four or five has rational coordinates.
Perfectness is not required, and the DVR is constructed inside the proof. -/
theorem cubic_coordinates_of_effective_degree_four_or_five_fg_positive
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [Field.FG k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨R, _, _, _, _, _, b, hb⟩ := hasCompleteCharZeroDVRLift_of_fg_positive ℓ k
  exact cubic_coordinates_of_effective_degree_four_or_five_over_DVR_residue
    (K := FractionRing R) b hb p hp hne z hz

/-- The rational coordinates give an actual section of the cubic surface
over the original finitely generated field. -/
theorem cubic_section_of_effective_degree_four_or_five_fg_positive
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [Field.FG k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp, a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨y, hy, he⟩ := cubic_coordinates_of_effective_degree_four_or_five_fg_positive
    ℓ p hp hne z hz
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy he
  exact ⟨a, by simpa using ha⟩

/-- Closed points of degree four or five suffice over every finitely
generated field of positive characteristic, including imperfect fields. -/
theorem cubic_section_of_closedPoint_degree_four_or_five_fg_positive
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [Field.FG k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 5) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp, a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  apply cubic_section_of_effective_degree_four_or_five_fg_positive ℓ p hp hne
    (Finsupp.single x 1)
  simpa [EffectiveZeroCycle.degree] using hx

end AllCharacteristics

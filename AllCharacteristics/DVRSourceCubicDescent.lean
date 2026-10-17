import AllCharacteristics.DVRSourceCycleLifting
import AllCharacteristics.SchemeCubicQuarticDescent
import AllCharacteristics.SchemeCubicDescent
import AllCharacteristics.HomogeneousSpecialization

/-!
# Degree-four and degree-five descent through a given mixed-characteristic DVR

Starting from the original smooth cubic and its effective cycle, construct the
smooth lift and a generic effective cycle of the same degree. The proved
characteristic-zero descent then gives a point, which specializes to the
original residue equation. No lifted family or lifted point is an input.
-/

open AlgebraicGeometry CategoryTheory IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective
universe u
variable {R k K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Field k] [Field K] [CharZero K]
  [Algebra R K] [IsFractionRing R K]

include K in
/-- An effective cycle of degree four or five on the original smooth cubic
gives a rational point if its field is the prescribed residue field of a
complete DVR with characteristic-zero fraction field. The family is constructed. -/
theorem cubic_coordinates_of_effective_degree_four_or_five_over_DVR_residue
    (b : R →+* k) (hb : Function.Surjective b)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨q, hq, he, _, _, w, hw⟩ := exists_smooth_lift_with_effectiveZeroCycle
    b hb (algebraMap R K) p hp hne z
  have hpoint : ∃ a : Spec (.of K) ⟶ hypersurface (q.map (algebraMap R K))
      (hq.map (algebraMap R K)),
      a ≫ hypersurfaceToBase (q.map (algebraMap R K)) (hq.map (algebraMap R K)) = 𝟙 _ := by
    rcases hz with h₄ | h₅
    · exact hypersurface_section_of_effective_degree_four _ _ w (hw.trans h₄)
    · exact hypersurface_section_of_effective_degree_five _ _ w (hw.trans h₅)
  obtain ⟨a, ha⟩ := hpoint
  obtain ⟨v, hv, hqv⟩ := hypersurface_coordinates_of_point (RingHom.id K)
    (q.map (algebraMap R K)) (hq.map (algebraMap R K)) a (by simpa using ha)
  have hgeneric : q.eval₂ (algebraMap R K) v = 0 := by
    rw [MvPolynomial.eval₂_eq_eval_map]
    exact hqv
  obtain ⟨y, hy, hqy⟩ := specialize_homogeneous_polynomial q hq b v hv hgeneric
  refine ⟨y, hy, ?_⟩
  rw [MvPolynomial.eval₂_eq_eval_map, he] at hqy
  exact hqy

include K in
/-- The residue-cubic solution is an actual rational section of its projective
structure morphism. -/
theorem cubic_section_of_effective_degree_four_or_five_over_DVR_residue
    (b : R →+* k) (hb : Function.Surjective b)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp, a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨y, hy, he⟩ := cubic_coordinates_of_effective_degree_four_or_five_over_DVR_residue
    (K := K) b hb p hp hne z hz
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy he
  exact ⟨a, by simpa using ha⟩

end AllCharacteristics

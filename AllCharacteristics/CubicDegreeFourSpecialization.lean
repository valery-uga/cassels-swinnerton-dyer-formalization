import AllCharacteristics.SchemeCubicQuarticDescent
import AllCharacteristics.HomogeneousRegularSpecialization

/-!
# Specialization of generic degree-four cycles

An actual effective degree-four cycle on the generic cubic gives a rational
point after reduction over an arbitrary regular local ring whose fraction
field has characteristic zero. There is no restriction on the residue
characteristic. The existence of the generic cycle is an explicit input;
constructing one from special-fiber data requires further geometry.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open HomogeneousProjective
universe u
variable {R K : Type u} [CommRing R] [IsRegularLocalRing R]
variable [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]

/-- A degree-four effective cycle on the generic cubic over a regular local
ring gives a nonzero solution of the reduced cubic in any residue
characteristic. The input cycle consists of actual scheme closed points. -/
theorem specialize_cubic_effective_degree_four_regularLocal
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    (z : EffectiveZeroCycle
      (hypersurface (p.map (algebraMap R K)) (hp.map (algebraMap R K))))
    (hz : EffectiveZeroCycle.degree
      (hypersurfaceToBase (p.map (algebraMap R K)) (hp.map (algebraMap R K))) z = 4) :
    ∃ y : Fin 4 → IsLocalRing.ResidueField R, y ≠ 0 ∧
      p.eval₂ (IsLocalRing.residue R) y = 0 := by
  obtain ⟨q, hq⟩ := hypersurface_section_of_effective_degree_four
    (p.map (algebraMap R K)) (hp.map (algebraMap R K)) z hz
  have hq' : q ≫ hypersurfaceToBase (p.map (algebraMap R K)) (hp.map (algebraMap R K)) =
      Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simpa using hq
  obtain ⟨x, hx, he⟩ := hypersurface_coordinates_of_point (RingHom.id K)
    (p.map (algebraMap R K)) (hp.map (algebraMap R K)) q hq'
  have he' : p.eval₂ (algebraMap R K) x = 0 := by
    simpa only [MvPolynomial.eval₂_map, RingHom.id_comp] using he
  exact specialize_homogeneous_equation_regularLocal p hp x hx he'

/-- A finite closed subscheme of rank four on the generic cubic supplies the
cycle needed for specialization, including when the subscheme is nonreduced. -/
theorem specialize_cubic_generic_subscheme_rank_four_regularLocal
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface (p.map (algebraMap R K)) (hp.map (algebraMap R K)))
    [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase (p.map (algebraMap R K)) (hp.map (algebraMap R K)))]
    (hi : finiteSchemeRank
      (i ≫ hypersurfaceToBase (p.map (algebraMap R K)) (hp.map (algebraMap R K))) = 4) :
    ∃ y : Fin 4 → IsLocalRing.ResidueField R, y ≠ 0 ∧
      p.eval₂ (IsLocalRing.residue R) y = 0 := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_closed_subscheme i
    (hypersurfaceToBase (p.map (algebraMap R K)) (hp.map (algebraMap R K)))
  exact specialize_cubic_effective_degree_four_regularLocal p hp z (hz.trans hi)

end AllCharacteristics

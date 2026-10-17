import PfaffianDescent.IntrinsicQuadraticIdealPiece
import PfaffianDescent.FiniteClosedImmersionRank
import AllCharacteristics.SectionFour

/-! The dimension-three statement for the FULL quadratic space of the
actual length-eight subscheme contained in a finite three-quadric net. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem intrinsicFullQuadraticSystem_finrank_eq_three_of_finite_triple
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))
    [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh)) = 8) :
    Module.finrank K (intrinsicFullQuadraticSystem
      (l ≫ quotientProjMap (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))) = 3 := by
  let T := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  obtain ⟨z, hz⟩ := AllCharacteristics.exists_effectiveZeroCycle_degree_finiteSchemeRank
    (l ≫ toBase T)
  obtain ⟨x, _, _⟩ := AllCharacteristics.EffectiveZeroCycle.exists_coprime_degree (l ≫ toBase T) z (by
    rw [hz, hZ]
    norm_num)
  have hT : Nonempty (scheme T) := Nonempty.map l ⟨x.1⟩
  have hseq := AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    f g h hf hg hh hT
  have hT8 : AllCharacteristics.finiteSchemeRank (toBase T) = 8 :=
    triple_quadrics_intersection_length_eight_of_regular_sequence f g h hf hg hh hseq
  letI : IsIso l := isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq
    l (toBase T) (hZ.trans hT8.symm)
  obtain ⟨hf0, hgreg, hhreg⟩ :=
    (triple_quadrics_isRegular_iff_sequential_regular f g h hf hg hh).mp hseq
  have hsocle : ∀ a : CoordinateRing T,
      (∀ j : Fin 4, coordinate T j * a = 0) → a = 0 :=
    triple_quadrics_no_irrelevant_annihilator f g h hf hg hh hf0
      (right_ne_zero_of_regular_mod_span_singleton
        (homogeneous_not_isUnit_of_pos_degree hf (by decide)) hgreg)
      (isRelPrime_of_regular_mod_span_singleton hf0 hgreg) hhreg
  rw [intrinsicFullQuadraticSystem_comp_isIso l (quotientProjMap T),
    intrinsicFullQuadraticSystem_eq_ideal_piece T hsocle, Submodule.finrank_map_subtype_eq]
  exact AllCharacteristics.sectionFour_triple_quadric_ideal_quadratic_piece_dimension_three_of_finite_of_nonempty
    f g h hf hg hh hT

set_option backward.isDefEq.respectTransparency false in
/-- The full quadratic-space statement with the original subscheme and
finite-net containment used by the manuscript, rather than a supplied lift. -/
theorem sectionFour_intrinsic_full_quadratic_dimension_three_of_finite_net
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase f hf) = 8) :
    Module.finrank K (intrinsicFullQuadraticSystem (i ≫ hypersurfaceToAmbient f hf)) = 3 := by
  let T := tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh
  let l := tripleCompleteIntersectionLift f g h hf hg hh i hker
  have hbase : l ≫ toBase T = i ≫ hypersurfaceToBase f hf := by
    rw [← tripleCompleteIntersectionToHypersurface_toBase f g h hf hg hh,
      ← Category.assoc, tripleCompleteIntersectionLift_fac]
  have hZl : AllCharacteristics.finiteSchemeRank (l ≫ toBase T) = 8 := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hbase,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hZ
  have hambient : l ≫ quotientProjMap T = i ≫ hypersurfaceToAmbient f hf := by
    rw [← tripleCompleteIntersectionToHypersurface_comp_hypersurfaceToAmbient
      f g h hf hg hh, ← Category.assoc, tripleCompleteIntersectionLift_fac]
  rw [← hambient]
  exact intrinsicFullQuadraticSystem_finrank_eq_three_of_finite_triple f g h hf hg hh l hZl

end PfaffianDescent

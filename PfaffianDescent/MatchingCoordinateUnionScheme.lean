import PfaffianDescent.MatchingCoordinateLineSchemes
import PfaffianDescent.LinearSubstitutedMatchingLinesInOriginalCubic

/-! SOURCE ONLY, UNVERIFIED. The ACTUAL union is cut out by the intersection
of the two coordinate line ideals. Containment transports through the actual
ambient GL isomorphism; no ground-field descent certificate is assumed. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def coordinateMatchingUnionIdeal :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) :=
  coordinateMatchingLineIdeal false ⊓ coordinateMatchingLineIdeal true

/-- Scheme union retains the full intersection ideal, not only the set union. -/
theorem coordinateMatchingUnion_range :
    Set.range (quotientProjMap (coordinateMatchingUnionIdeal (K := K))) =
      Set.range (quotientProjMap (coordinateMatchingLineIdeal (K := K) false)) ∪
      Set.range (quotientProjMap (coordinateMatchingLineIdeal (K := K) true)) := by
  rw [range_quotientProjMap, range_quotientProjMap, range_quotientProjMap]
  simpa only [coordinateMatchingUnionIdeal, HomogeneousIdeal.toIdeal_inf] using
    ProjectiveSpectrum.zeroLocus_inf (homogeneousSubmodule (Fin 4) K)
      (coordinateMatchingLineIdeal (K := K) false).toIdeal
      (coordinateMatchingLineIdeal (K := K) true).toIdeal

/-- The two projective coordinate lines are disjoint, over every field. -/
theorem coordinateMatchingLines_disjoint :
    Disjoint
      (Set.range (quotientProjMap (coordinateMatchingLineIdeal (K := K) false)))
      (Set.range (quotientProjMap (coordinateMatchingLineIdeal (K := K) true))) := by
  rw [Set.disjoint_left]
  intro z hz0 hz1
  rw [range_quotientProjMap] at hz0 hz1
  have h0 := (ProjectiveSpectrum.mem_zeroLocus
    (homogeneousSubmodule (Fin 4) K) z _).mp hz0
  have h1 := (ProjectiveSpectrum.mem_zeroLocus
    (homogeneousSubmodule (Fin 4) K) z _).mp hz1
  have hX (r : Fin 4) : X r ∈ z.asHomogeneousIdeal.toIdeal := by
    fin_cases r
    · apply h1
      change X 0 ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) K))
      exact Ideal.subset_span (by simp)
    · apply h1
      change X 1 ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) K))
      exact Ideal.subset_span (by simp)
    · apply h0
      change X 2 ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) K))
      exact Ideal.subset_span (by simp)
    · apply h0
      change X 3 ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) K))
      exact Ideal.subset_span (by simp)
  have hspan : (HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin 4) K)).toIdeal ≤
      Ideal.span (Set.range (X : Fin 4 → MvPolynomial (Fin 4) K)) := by
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro n hn p hp
    change p ∈ MvPolynomial.idealOfVars (Fin 4) K
    rw [← pow_one (MvPolynomial.idealOfVars (Fin 4) K), MvPolynomial.mem_pow_idealOfVars_iff]
    intro m hm
    have he : m.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hm).symm
    exact he ▸ hn
  apply z.not_irrelevant_le
  change (HomogeneousIdeal.irrelevant
    (homogeneousSubmodule (Fin 4) K)).toIdeal ≤ z.asHomogeneousIdeal.toIdeal
  refine hspan.trans (Ideal.span_le.mpr ?_)
  rintro p ⟨r, rfl⟩
  exact hX r

/-- Actual union containment follows from the two length-four restrictions,
not from any rational-point theorem. -/
theorem equationIdeal_le_matchingUnion_of_skew_double_points
    (a f : K) (ha : a ≠ 0) (hf : f ≠ 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : ∀ r, aeval (tangentDualPoint
      (skewTangentDirections a 0 0 0 0 f) r) F = 0) :
    (equationIdeal F hF).toIdeal ≤ (coordinateMatchingUnionIdeal (K := K)).toIdeal := by
  obtain ⟨h01, h23⟩ := cubic_contains_matching_lines_of_skew_matrix a f ha hf F hF hvan
  change (equationIdeal F hF).toIdeal ≤
    (coordinateMatchingLineIdeal (K := K) false).toIdeal ⊓
      (coordinateMatchingLineIdeal (K := K) true).toIdeal
  exact le_inf
    (equationIdeal_le_coordinateMatchingLineIdeal false F hF h01)
    (equationIdeal_le_coordinateMatchingLineIdeal true F hF h23)

/-- The union source embeds into the SAME original cubic. The coordinate
normal form and its actual double-point vanishing are legitimate matching
branch data; no containment/union-descent certificate is an input. -/
theorem linearSubstituted_matching_union_in_original_cubic
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (a f : K) (ha : a ≠ 0) (hf : f ≠ 0)
    (hvan : ∀ r, aeval (tangentDualPoint
      (skewTangentDirections a 0 0 0 0 f) r) (linearSubstitution M F) = 0) :
    ∃ c : scheme (coordinateMatchingUnionIdeal (K := K)) ⟶ hypersurface F hF,
      IsClosedImmersion c ∧ c ≫ quotientProjMap (equationIdeal F hF) =
        quotientProjMap (coordinateMatchingUnionIdeal (K := K)) ≫
          (linearCoordinateChangeAmbientIso M hM).inv := by
  let G := linearSubstitution M F
  let hG := linearSubstitution_homogeneous M hF
  let I := equationIdeal F hF
  let J := equationIdeal G hG
  have hIJ : J.toIdeal = I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom := by
    change Ideal.span ({G} : Set (MvPolynomial (Fin 4) K)) =
      (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).map
        (linearSubstitutionEquiv M hM).toRingHom
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let e := linearCoordinateChangeSchemeIso M hM I J hIJ
  let alpha := linearCoordinateChangeAmbientIso M hM
  have hAmbient : e.hom ≫ quotientProjMap J = quotientProjMap I ≫ alpha.hom :=
    linearCoordinateChangeSchemeIso_hom_toAmbient M hM I J hIJ
  have hInv : e.inv ≫ quotientProjMap I = quotientProjMap J ≫ alpha.inv := by
    apply (cancel_mono alpha.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hAmbient, Iso.inv_hom_id_assoc]
  have hContain : J.toIdeal ≤ (coordinateMatchingUnionIdeal (K := K)).toIdeal :=
    equationIdeal_le_matchingUnion_of_skew_double_points a f ha hf G hG hvan
  letI : IsClosedImmersion
      (schemeQuotientMap J (coordinateMatchingUnionIdeal (K := K)) hContain) :=
    schemeQuotientMap_closedImmersion _ _ _
  let c := schemeQuotientMap J (coordinateMatchingUnionIdeal (K := K)) hContain ≫ e.inv
  refine ⟨c, ?_, ?_⟩
  · dsimp only [c]
    infer_instance
  · change (schemeQuotientMap J (coordinateMatchingUnionIdeal (K := K)) hContain ≫
      e.inv) ≫ quotientProjMap I = _
    rw [Category.assoc, hInv, ← Category.assoc,
      schemeQuotientMap_comp_quotientProjMap]

end PfaffianDescent.QuarticNet

import PfaffianDescent.ActualMatchingQuadraticLineProjectiveIso
import PfaffianDescent.MatchingCoordinateUnionScheme
import AllCharacteristics.ProjectiveBaseChange

/-! SOURCE ONLY / UNVERIFIED. The two complementary projector ideals are
actual disjoint projective lines over the SAME coefficient field. Their
original geometric line ideals and categorical base changes are retained. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private def matchingPairSwap : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

theorem matchingEdgeProjectorMatrix_pairSwap
    {K : Type u} [Field K] (B : Basis (Fin 4) K (Fin 4 → K)) :
    matchingEdgeProjectorMatrix (B.reindex matchingPairSwap) =
      1 - matchingEdgeProjectorMatrix B := by
  ext m n
  rw [matchingEdgeProjectorMatrix_complement_entry]
  have h0 : matchingPairSwap.symm 0 = 2 := by decide
  have h1 : matchingPairSwap.symm 1 = 3 := by decide
  change (B.reindex matchingPairSwap) 0 m *
      (B.reindex matchingPairSwap).repr (Pi.single n 1) 0 +
      (B.reindex matchingPairSwap) 1 m *
        (B.reindex matchingPairSwap).repr (Pi.single n 1) 1 = _
  simp only [Basis.reindex_apply, Basis.repr_reindex_apply, h0, h1]

def matchingSideProjector {K : Type u} [Field K]
    (P : Matrix (Fin 4) (Fin 4) K) (side : Bool) :
    Matrix (Fin 4) (Fin 4) K := if side then 1 - P else P

theorem matchingSideProjector_map {E K : Type u} [Field E] [Field K]
    (f : E →+* K) (P : Matrix (Fin 4) (Fin 4) E) (side : Bool) :
    (matchingSideProjector P side).map f = matchingSideProjector (P.map f) side := by
  cases side
  · rfl
  · ext m n
    simp only [matchingSideProjector, Bool.true_eq, if_true,
      Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp

/-- Both lines, not just the first one, are genuine P1 over E. -/
theorem intermediateMatchingBothLines_projectiveLine_isos
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K) (P : Matrix (Fin 4) (Fin 4) E)
    (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B) :
    ∀ side : Bool,
      ∃ e : scheme (projectorLineIdeal (matchingSideProjector P side)) ≅
          Proj (homogeneousSubmodule (Fin 2) E),
        e.hom ≫ ambientToBase (R := E) (σ := Fin 2) =
          toBase (projectorLineIdeal (matchingSideProjector P side)) := by
  intro side
  cases side
  · obtain ⟨C, hC, e, he, _⟩ := intermediateMatchingLine_projectiveLine_iso E P B hP
    exact ⟨e, he⟩
  · let B' := B.reindex matchingPairSwap
    have hComp : (1 - P).map E.val.toRingHom = matchingEdgeProjectorMatrix B' := by
      rw [show (1 - P).map E.val.toRingHom = 1 - P.map E.val.toRingHom from
        matchingSideProjector_map E.val.toRingHom P true,
        hP, ← matchingEdgeProjectorMatrix_pairSwap B]
    obtain ⟨C, hC, e, he, _⟩ :=
      intermediateMatchingLine_projectiveLine_iso E (1 - P) B' hComp
    exact ⟨e, he⟩

/-- Complementary projector line equations have no common projective point.
This proof works in characteristic2 and does not use a rational-point result. -/
theorem complementaryProjectorLines_disjoint
    {E : Type u} [Field E] (P : Matrix (Fin 4) (Fin 4) E) :
    Disjoint (Set.range (quotientProjMap (projectorLineIdeal P)))
      (Set.range (quotientProjMap (projectorLineIdeal (1 - P)))) := by
  rw [Set.disjoint_left]
  intro z hz0 hz1
  rw [range_quotientProjMap] at hz0 hz1
  have h0 := (ProjectiveSpectrum.mem_zeroLocus
    (homogeneousSubmodule (Fin 4) E) z _).mp hz0
  have h1 := (ProjectiveSpectrum.mem_zeroLocus
    (homogeneousSubmodule (Fin 4) E) z _).mp hz1
  have hX (r : Fin 4) : X r ∈ z.asHomogeneousIdeal.toIdeal := by
    have hLeft : linearCoordinate (1 - P) r ∈ z.asHomogeneousIdeal.toIdeal :=
      h0 (Ideal.subset_span ⟨r, rfl⟩)
    have hRight : linearCoordinate P r ∈ z.asHomogeneousIdeal.toIdeal := by
      apply h1
      change linearCoordinate P r ∈
        Ideal.span (Set.range (linearCoordinate (1 - (1 - P))))
      rw [show 1 - (1 - P) = P from by abel]
      exact Ideal.subset_span ⟨r, rfl⟩
    have hSum : linearCoordinate (1 - P) r + linearCoordinate P r = X r := by
      simp only [linearCoordinate, Matrix.map_sub _ (map_sub _),
        Matrix.sub_mulVec, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec, Pi.sub_apply]
      abel
    rw [← hSum]
    exact Ideal.add_mem _ hLeft hRight
  have hspan : (HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin 4) E)).toIdeal ≤
      Ideal.span (Set.range (X : Fin 4 → MvPolynomial (Fin 4) E)) := by
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro n hn p hp
    change p ∈ MvPolynomial.idealOfVars (Fin 4) E
    rw [← pow_one (MvPolynomial.idealOfVars (Fin 4) E), MvPolynomial.mem_pow_idealOfVars_iff]
    intro m hm
    have he : m.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hm).symm
    exact he ▸ hn
  apply z.not_irrelevant_le
  change (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) E)).toIdeal ≤
    z.asHomogeneousIdeal.toIdeal
  exact hspan.trans (Ideal.span_le.mpr (by rintro p ⟨r, rfl⟩; exact hX r))

/-- Each E-line extends to the exact original geometric matching line ideal.
The accompanying actual projective coefficient map is Cartesian. -/
theorem intermediateMatchingBothLines_original_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K) (P : Matrix (Fin 4) (Fin 4) E)
    (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B) :
    ∀ side : Bool,
      let IE := projectorLineIdeal (matchingSideProjector P side)
      let IK := projectorLineIdeal (matchingSideProjector (matchingEdgeProjectorMatrix B) side)
      ∃ hBC : IE.toIdeal.map (MvPolynomial.map E.val.toRingHom) = IK.toIdeal,
        IK.toIdeal = (coordinateMatchingLineIdeal (K := K) side).toIdeal.map
          (linearSubstitution (basisCoordinateMatrix B)⁻¹).toRingHom ∧
        IsPullback (projectiveCoefficientMap E.val.toRingHom IE IK hBC)
          (toBase IK) (toBase IE) (Spec.map (CommRingCat.ofHom E.val.toRingHom)) := by
  intro side
  dsimp only
  have hBC : (projectorLineIdeal (matchingSideProjector P side)).toIdeal.map
      (MvPolynomial.map E.val.toRingHom) =
    (projectorLineIdeal (matchingSideProjector (matchingEdgeProjectorMatrix B) side)).toIdeal := by
    rw [projectorLineIdeal_baseChange, matchingSideProjector_map, hP]
  refine ⟨hBC, ?_, isPullback_projectiveCoefficientMap _ _ _ hBC⟩
  cases side
  · exact projectorLineIdeal_eq_originalMatchingLine B
  · exact projectorComplementLineIdeal_eq_originalMatchingLine B

end PfaffianDescent.QuarticNet

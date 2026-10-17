import PfaffianDescent.FourCoordinateVertexSuppliedLiteralComponent
import PfaffianDescent.FourCoordinateVertexWholeSchemeCoproductIso

/-! SOURCE-ONLY UNVERIFIED isolated whole-source wrapper. This alternative
split imports the shared component declarations, avoiding duplicate names. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For a separately supplied WHOLE Z, derive its source isomorphism from
the actual disjoint rank-two components, and retain the supplied U. -/
theorem fourCoordinateVertex_whole_supplied_presentation_square
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z) [∀ r, IsClosedImmersion (c r)]
    (hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)))
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2)
    (hWhole : AllCharacteristics.finiteSchemeRank (i ≫ toBase ⊥) = 8)
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (eRow : ∀ r, Y r ≅ Spec (.of (DualNumber K)))
    (hpoint : ∀ r, (eRow r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hdiag]) =
          (c r ≫ i) ≫ quotientProjMap ⊥) :
    ∃ e : Z ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)),
      e.hom ≫ (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) =
        i ≫ quotientProjMap ⊥ := by
  let j := Sigma.desc c
  letI : IsIso j := fourCoordinateVertex_wholeScheme_canonicalCoproduct_isIso
    i Y c hDisjoint hSupport hComponents hWhole
  obtain ⟨eSum, hfac⟩ := fourCoordinateVertex_supplied_presentation_square
    Y (fun r => c r ≫ i) U hdiag eRow hpoint
  have hSum : Sigma.desc (fun r => (c r ≫ i) ≫ quotientProjMap ⊥) =
      j ≫ (i ≫ quotientProjMap ⊥) := by
    apply Sigma.hom_ext
    intro r
    simp only [j, Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
  refine ⟨(asIso j).symm ≪≫ eSum, ?_⟩
  change (inv j ≫ eSum.hom) ≫
    (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) = _
  rw [Category.assoc, hfac, hSum, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- The IFF uses the supplied matrix, including possible zero entries and
individual zero relation weights. It is not a statement about a choice. -/
theorem fourCoordinateVertex_whole_supplied_intrinsic_weighted_iff
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z) [∀ r, IsClosedImmersion (c r)]
    (hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)))
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2)
    (hWhole : AllCharacteristics.finiteSchemeRank (i ≫ toBase ⊥) = 8)
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (eRow : ∀ r, Y r ≅ Spec (.of (DualNumber K)))
    (hpoint : ∀ r, (eRow r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hdiag]) =
          (c r ≫ i) ≫ quotientProjMap ⊥) :
    3 ≤ finrank K (intrinsicFullQuadraticSystem (i ≫ quotientProjMap ⊥)) ↔
      ∃ w : Fin 4 → K, w ≠ 0 ∧
        ∀ r s, r < s → w r * U r s = -(w s * U s r) := by
  obtain ⟨e, hfac⟩ := fourCoordinateVertex_whole_supplied_presentation_square
    i Y c hDisjoint hSupport hComponents hWhole U hdiag eRow hpoint
  exact suppliedFourTangent_intrinsic_weighted_iff _ U hdiag e hfac

/-- Literal supplied-skew base-locus conclusion for the SAME whole Z and
its intrinsic FULL quadratic ideal, not a new scheme with the same points. -/
theorem fourCoordinateVertex_whole_supplied_intrinsic_fullBase_alternative
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z) [∀ r, IsClosedImmersion (c r)]
    (hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)))
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2)
    (hWhole : AllCharacteristics.finiteSchemeRank (i ≫ toBase ⊥) = 8)
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (eRow : ∀ r, Y r ≅ Spec (.of (DualNumber K)))
    (hpoint : ∀ r, (eRow r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hdiag]) =
          (c r ≫ i) ≫ quotientProjMap ⊥)
    (hskew : ∀ r s, U r s = -U s r)
    (hnonzero : ∀ r s, r ≠ s → U r s ≠ 0) :
    QuarticNet.IntrinsicFullBaseEmbeddedAlternative (i ≫ quotientProjMap ⊥) := by
  obtain ⟨e, hfac⟩ := fourCoordinateVertex_whole_supplied_presentation_square
    i Y c hDisjoint hSupport hComponents hWhole U hdiag eRow hpoint
  exact suppliedFourTangent_intrinsic_fullBase_alternative _ U hdiag e hfac hskew hnonzero


end PfaffianDescent

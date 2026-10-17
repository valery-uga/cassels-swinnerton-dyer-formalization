import PfaffianDescent.FourCoordinateVertexActualLiteralComponent
import PfaffianDescent.FourCoordinateVertexSuppliedWholeLiteral

/-! SOURCE ONLY, UNVERIFIED. Minimal whole-original-Z choice-independent
geometric adapter. Its ONLY factory inputs are actual rank-two components,
actual vertex support, disjointness and rank8. Every source Iso and ambient
presentation square is constructed or quantified in the OUTPUT. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fourCoordinateVertex_whole_actual_choice_independent_literal_presentation
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z) [∀ r, IsClosedImmersion (c r)]
    (hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)))
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2)
    (hWhole : AllCharacteristics.finiteSchemeRank (i ≫ toBase ⊥) = 8) :
    ∃ (U : Fin 4 → Fin 4 → K) (eOne : ∀ r, Y r ≅ Spec (.of (DualNumber K)))
      (hUdiag : ∀ r, U r r = 0),
      (∀ r, U r ≠ 0) ∧
      (∀ r, (eOne r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => inl (coordinateVertexCoordinates (K := K) r s) + inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hUdiag]) =
          (c r ≫ i) ≫ quotientProjMap ⊥) ∧
      ∀ (V : Fin 4 → Fin 4 → K) (hVdiag : ∀ r, V r r = 0)
        (eTwo : ∀ r, Y r ≅ Spec (.of (DualNumber K))),
      (∀ r, (eTwo r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => inl (coordinateVertexCoordinates (K := K) r s) + inr (V r s)) r
        (by simp [coordinateVertexCoordinates, hVdiag]) =
          (c r ≫ i) ≫ quotientProjMap ⊥) →
      ∃ (epsilon : Fin 4 → K) (hepsilon : ∀ r, epsilon r ≠ 0),
        V = QuarticNet.rescaleTangentDirections epsilon U ∧
        (∀ r, (eTwo r).hom ≫ Spec.map (CommRingCat.ofHom
          (QuarticNet.dualNumberRescaleEquiv (epsilon r) (hepsilon r)).toRingHom) =
            (eOne r).hom) ∧
        ∃ eWhole : Z ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)),
          eWhole.hom ≫ (QuarticNet.fourTangentDualToProjective V ≫ quotientProjMap ⊥) =
            i ≫ quotientProjMap ⊥ ∧
          (3 ≤ finrank K (intrinsicFullQuadraticSystem (i ≫ quotientProjMap ⊥)) ↔
            ∃ w : Fin 4 → K, w ≠ 0 ∧
              ∀ r s, r < s → w r * V r s = -(w s * V s r)) ∧
          ((∀ r s, V r s = -V s r) → (∀ r s, r ≠ s → V r s ≠ 0) →
            QuarticNet.IntrinsicFullBaseEmbeddedAlternative (i ≫ quotientProjMap ⊥)) := by
  classical
  letI : ∀ r, IsClosedImmersion (c r ≫ i) := fun r => inferInstance
  letI : ∀ r, IsFinite ((c r ≫ i) ≫ toBase ⊥) := by
    intro r
    rw [Category.assoc]
    infer_instance
  have hComponents' : ∀ r, AllCharacteristics.finiteSchemeRank
      ((c r ≫ i) ≫ toBase ⊥) = 2 := by
    intro r
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, Category.assoc,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hComponents r
  obtain ⟨U, eOne, hUdiag, hRows, hOne, hEvery⟩ :=
    fourCoordinateVertex_actual_exists_choice_independent_literal_presentation
      Y (fun r => c r ≫ i) hSupport hComponents'
  refine ⟨U, eOne, hUdiag, hRows, hOne, ?_⟩
  intro V hVdiag eTwo hTwo
  obtain ⟨epsilon, hepsilon, hEq, hSource, _, _⟩ := hEvery V hVdiag eTwo hTwo
  obtain ⟨eWhole, hWholeSquare⟩ := fourCoordinateVertex_whole_supplied_presentation_square
    i Y c hDisjoint hSupport hComponents hWhole V hVdiag eTwo hTwo
  refine ⟨epsilon, hepsilon, hEq, hSource, eWhole, hWholeSquare,
    suppliedFourTangent_intrinsic_weighted_iff _ V hVdiag eWhole hWholeSquare, ?_⟩
  intro hSkew hFull
  exact suppliedFourTangent_intrinsic_fullBase_alternative _ V hVdiag
    eWhole hWholeSquare hSkew hFull

end PfaffianDescent

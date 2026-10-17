import PfaffianDescent.FourCoordinateVertexActualChoiceIndependentWhole
import PfaffianDescent.ActualP3IdealQuadraticGlobalBase

/-! SOURCE ONLY, UNVERIFIED. CHECK ONLY AFTER the actual arbitrary-Z H0
dictionary is accepted. The dictionary is called internally for the SAME
original closed immersion; no comparison/equivalence is a factory premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fourCoordinateVertex_whole_actual_choice_independent_H0_literal_presentation
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
      (3 ≤ finrank K (ActualP3IdealQuadraticHZero (i ≫ quotientProjMap ⊥)) ↔
        ∃ w : Fin 4 → K, w ≠ 0 ∧
          ∀ r s, r < s → w r * V r s = -(w s * V s r)) ∧
      ((∀ r s, V r s = -V s r) → (∀ r s, r ≠ s → V r s ≠ 0) →
        (∃ l : Z ⟶ scheme (p3ActualIdealQuadraticGlobalBaseIdeal (i ≫ quotientProjMap ⊥)),
          IsIso l ∧ l ≫ quotientProjMap
            (p3ActualIdealQuadraticGlobalBaseIdeal (i ≫ quotientProjMap ⊥)) =
              i ≫ quotientProjMap ⊥) ∨
        QuarticNet.GroundTwistedCubicPresentation
          (p3ActualIdealQuadraticGlobalBaseIdeal (i ≫ quotientProjMap ⊥))) := by
  classical
  obtain ⟨U, eOne, hUdiag, hRows, hOne, hEvery⟩ :=
    fourCoordinateVertex_whole_actual_choice_independent_literal_presentation
      i Y c hDisjoint hSupport hComponents hWhole
  refine ⟨U, eOne, hUdiag, hRows, hOne, ?_⟩
  intro V hVdiag eTwo hTwo
  obtain ⟨epsilon, hepsilon, hEq, hSource, eWhole, hWholeSquare, hIff, hBase⟩ :=
    hEvery V hVdiag eTwo hTwo
  refine ⟨?_, ?_⟩
  · change (3 ≤ finrank K (SchemeModuleGlobalSectionsOver
        (ambientToBase (R := K) (σ := Fin 4))
        (closedImmersionIdealTwist (i ≫ quotientProjMap ⊥)
          (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) ↔ _)
    rw [p3ActualIdealQuadratic_finrank_eq_intrinsic (i ≫ quotientProjMap ⊥)]
    exact hIff
  · intro hSkew hFull
    rw [p3ActualIdealQuadraticGlobalBaseIdeal_eq_intrinsic]
    exact hBase hSkew hFull

end PfaffianDescent

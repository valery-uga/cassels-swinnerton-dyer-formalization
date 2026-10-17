import PfaffianDescent.FourCoordinateVertexSuppliedWholeLiteral
import PfaffianDescent.ActualP3IdealQuadraticGlobalBase

/-! SOURCE ONLY, UNVERIFIED. Literal consumers of a SUPPLIED epsilon
representation on SAME actual components. eRow/hpoint below encode that
literal representation, not a desired canonical comparison or whole-Z Iso.
The whole-Z Iso is derived internally by the structural rank/support
factory. The preceding ActualH0LiteralWhole file constructs reference data
with NO representation input and universally covers every such supplied
representation. Both declarations below apply H0 only to actual closed i. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fourCoordinateVertex_whole_supplied_actual_H0_weighted_iff
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
    3 ≤ finrank K (ActualP3IdealQuadraticHZero (i ≫ quotientProjMap ⊥)) ↔
      ∃ w : Fin 4 → K, w ≠ 0 ∧
        ∀ r s, r < s → w r * U r s = -(w s * U s r) := by
  change (3 ≤ finrank K (SchemeModuleGlobalSectionsOver
    (ambientToBase (R := K) (σ := Fin 4))
    (closedImmersionIdealTwist (i ≫ quotientProjMap ⊥)
      (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) ↔ _)
  rw [p3ActualIdealQuadratic_finrank_eq_intrinsic (i ≫ quotientProjMap ⊥)]
  exact fourCoordinateVertex_whole_supplied_intrinsic_weighted_iff
    i Y c hDisjoint hSupport hComponents hWhole U hdiag eRow hpoint

theorem fourCoordinateVertex_whole_supplied_actual_H0_fullBase_alternative
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
    (∃ l : Z ⟶ scheme (p3ActualIdealQuadraticGlobalBaseIdeal (i ≫ quotientProjMap ⊥)),
      IsIso l ∧ l ≫ quotientProjMap
        (p3ActualIdealQuadraticGlobalBaseIdeal (i ≫ quotientProjMap ⊥)) =
          i ≫ quotientProjMap ⊥) ∨
      QuarticNet.GroundTwistedCubicPresentation
        (p3ActualIdealQuadraticGlobalBaseIdeal (i ≫ quotientProjMap ⊥)) := by
  rw [p3ActualIdealQuadraticGlobalBaseIdeal_eq_intrinsic]
  exact fourCoordinateVertex_whole_supplied_intrinsic_fullBase_alternative
    i Y c hDisjoint hSupport hComponents hWhole U hdiag eRow hpoint hskew hnonzero

end PfaffianDescent

import PfaffianDescent.FourCoordinateVertexIntrinsicWeightedRelations
import PfaffianDescent.FourCoordinateVertexWholeSchemeCoproductIso

/-! The weighted skew IFF on a separately supplied whole length-eight scheme.
The true canonical coproduct isomorphism transfers its full intrinsic system;
there is no full off-diagonal support or skewness hypothesis. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

def fourCoordinateVertexWholeActualWeightedTangentMatrix
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z) [∀ r, IsClosedImmersion (c r)]
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2) :
    Fin 4 → Fin 4 → K := by
  letI : ∀ r, IsClosedImmersion (c r ≫ i) := fun r => inferInstance
  letI : ∀ r, IsFinite ((c r ≫ i) ≫ toBase ⊥) := by
    intro r
    rw [Category.assoc]
    infer_instance
  have hComponents' : ∀ r, AllCharacteristics.finiteSchemeRank ((c r ≫ i) ≫ toBase ⊥) = 2 := by
    intro r
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, Category.assoc,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hComponents r
  exact fourCoordinateVertexActualWeightedTangentMatrix Y (fun r => c r ≫ i)
    hSupport hComponents'

/-- Literal weighted relations for the full intrinsic quadratic system of
an actual whole scheme, with its four supplied rank-two components. -/
theorem fourCoordinateVertex_whole_intrinsicQuadraticSystem_finrank_ge_three_iff
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z) [∀ r, IsClosedImmersion (c r)]
    (hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)))
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2)
    (hWhole : AllCharacteristics.finiteSchemeRank (i ≫ toBase ⊥) = 8) :
    3 ≤ finrank K (intrinsicFullQuadraticSystem (i ≫ quotientProjMap ⊥)) ↔
      ∃ w : Fin 4 → K, w ≠ 0 ∧ ∀ r s, r < s →
        w r * fourCoordinateVertexWholeActualWeightedTangentMatrix i Y c hSupport hComponents r s =
          -(w s * fourCoordinateVertexWholeActualWeightedTangentMatrix i Y c hSupport hComponents s r) := by
  letI : ∀ r, IsClosedImmersion (c r ≫ i) := fun r => inferInstance
  letI : ∀ r, IsFinite ((c r ≫ i) ≫ toBase ⊥) := by
    intro r
    rw [Category.assoc]
    infer_instance
  have hComponents' : ∀ r, AllCharacteristics.finiteSchemeRank ((c r ≫ i) ≫ toBase ⊥) = 2 := by
    intro r
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, Category.assoc,
      ← AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact hComponents r
  let j := Sigma.desc c
  letI : IsIso j := fourCoordinateVertex_wholeScheme_canonicalCoproduct_isIso
    i Y c hDisjoint hSupport hComponents hWhole
  have hSum : Sigma.desc (fun r => (c r ≫ i) ≫ quotientProjMap ⊥) =
      j ≫ (i ≫ quotientProjMap ⊥) := by
    apply Sigma.hom_ext
    intro r
    simp only [j, Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
  have hSystem : intrinsicFullQuadraticSystem
      (Sigma.desc (fun r => (c r ≫ i) ≫ quotientProjMap ⊥)) =
      intrinsicFullQuadraticSystem (i ≫ quotientProjMap ⊥) := by
    rw [hSum, intrinsicFullQuadraticSystem_comp_isIso]
  have h := fourCoordinateVertex_actual_intrinsicQuadraticSystem_finrank_ge_three_iff
    Y (fun r => c r ≫ i) hSupport hComponents'
  rw [hSystem] at h
  exact h

end PfaffianDescent

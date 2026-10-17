import PfaffianDescent.FourCoordinateVertexActualSchemePresentation
import PfaffianDescent.FourTangentIntrinsicWeightedRelations
import PfaffianDescent.IntrinsicQuadraticIdealPiece

/-! The literal weighted skew IFF for four supplied length-two schemes at
coordinate vertices. Their tangent representatives and the exact ambient
presentation are derived from the schemes. Zero entries and weights are allowed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

def fourCoordinateVertexActualWeightedTangentMatrix
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [∀ r, IsClosedImmersion (i r)] [∀ r, IsFinite (i r ≫ toBase ⊥)]
    (hSupport : ∀ r, Set.range (i r) = {coordinateVertex (K := K) r})
    (hZ : ∀ r, AllCharacteristics.finiteSchemeRank (i r ≫ toBase ⊥) = 2) :
    Fin 4 → Fin 4 → K :=
  Classical.choose (fourCoordinateVertex_actual_scheme_presentation Z i hSupport hZ)

/-- Manuscript Lemma `lem:uij-skew-symmetric`, on the full intrinsic
quadratic system of the actual supplied four components. -/
theorem fourCoordinateVertex_actual_intrinsicQuadraticSystem_finrank_ge_three_iff
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [∀ r, IsClosedImmersion (i r)] [∀ r, IsFinite (i r ≫ toBase ⊥)]
    (hSupport : ∀ r, Set.range (i r) = {coordinateVertex (K := K) r})
    (hZ : ∀ r, AllCharacteristics.finiteSchemeRank (i r ≫ toBase ⊥) = 2) :
    3 ≤ finrank K (intrinsicFullQuadraticSystem
      (Sigma.desc (fun r => i r ≫ quotientProjMap ⊥))) ↔
      ∃ w : Fin 4 → K, w ≠ 0 ∧ ∀ r s, r < s →
        w r * fourCoordinateVertexActualWeightedTangentMatrix Z i hSupport hZ r s =
          -(w s * fourCoordinateVertexActualWeightedTangentMatrix Z i hSupport hZ s r) := by
  let U := fourCoordinateVertexActualWeightedTangentMatrix Z i hSupport hZ
  obtain ⟨e, hdiag, hrows, hfac⟩ :=
    Classical.choose_spec (fourCoordinateVertex_actual_scheme_presentation Z i hSupport hZ)
  have hfac' : e.hom ≫ (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))) =
      Sigma.desc (fun r => i r ≫ quotientProjMap ⊥) := hfac
  rw [← hfac', intrinsicFullQuadraticSystem_comp_isIso]
  exact QuarticNet.fourTangent_intrinsicQuadraticSystem_finrank_ge_three_iff U hdiag

/-- The same IFF together with its derived actual tangent presentation. -/
theorem fourCoordinateVertex_actual_weightedSkew_presentation
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [∀ r, IsClosedImmersion (i r)] [∀ r, IsFinite (i r ≫ toBase ⊥)]
    (hSupport : ∀ r, Set.range (i r) = {coordinateVertex (K := K) r})
    (hZ : ∀ r, AllCharacteristics.finiteSchemeRank (i r ≫ toBase ⊥) = 2) :
    ∃ (U : Fin 4 → Fin 4 → K)
      (e : (∐ Z) ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K))),
      (∀ r, U r r = 0) ∧ (∀ r, U r ≠ 0) ∧
      e.hom ≫ (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) =
        Sigma.desc (fun r => i r ≫ quotientProjMap ⊥) ∧
      (3 ≤ finrank K (intrinsicFullQuadraticSystem
        (Sigma.desc (fun r => i r ≫ quotientProjMap ⊥))) ↔
        ∃ w : Fin 4 → K, w ≠ 0 ∧
          ∀ r s, r < s → w r * U r s = -(w s * U s r)) := by
  let U := fourCoordinateVertexActualWeightedTangentMatrix Z i hSupport hZ
  obtain ⟨e, hdiag, hrows, hfac⟩ :=
    Classical.choose_spec (fourCoordinateVertex_actual_scheme_presentation Z i hSupport hZ)
  refine ⟨U, e, hdiag, hrows, hfac, ?_⟩
  exact fourCoordinateVertex_actual_intrinsicQuadraticSystem_finrank_ge_three_iff
    Z i hSupport hZ

end PfaffianDescent

import PfaffianDescent.CoordinateVertexLengthTwoActualTangent

/-! SOURCE-ONLY UNVERIFIED isolated check unit. This is an alternative
split of the previously supplied TMP draft, with the same declarations.
Do not import the old monolithic version alongside this split. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable [IsAlgClosed K]

/-- Thin rowwise consumer of the EXISTING actual rank-two provider. -/
theorem fourCoordinateVertex_actual_exists_epsilon_presentations
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [∀ r, IsClosedImmersion (i r)] [∀ r, IsFinite (i r ≫ toBase ⊥)]
    (hSupport : ∀ r, Set.range (i r) = {coordinateVertex (K := K) r})
    (hZ : ∀ r, AllCharacteristics.finiteSchemeRank (i r ≫ toBase ⊥) = 2) :
    ∃ (U : Fin 4 → Fin 4 → K)
      (eRow : ∀ r, Z r ≅ Spec (.of (DualNumber K))) (hdiag : ∀ r, U r r = 0),
      (∀ r, U r ≠ 0) ∧
      ∀ r, (eRow r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hdiag]) = i r ≫ quotientProjMap ⊥ := by
  classical
  have hEach (r : Fin 4) := coordinateVertex_lengthTwo_actual_tangent
    (i r) r (hSupport r) (hZ r)
  choose eRow U hdiag hRows hpoint using hEach
  exact ⟨U, eRow, hdiag, hRows, hpoint⟩

end PfaffianDescent

import PfaffianDescent.FourTangentSuppliedPresentationLiteral

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

theorem fourCoordinateVertex_supplied_intrinsic_weighted_iff
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (eRow : ∀ r, Z r ≅ Spec (.of (DualNumber K)))
    (hpoint : ∀ r, (eRow r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hdiag]) = i r ≫ quotientProjMap ⊥) :
    3 ≤ finrank K (intrinsicFullQuadraticSystem
      (Sigma.desc (fun r => i r ≫ quotientProjMap ⊥))) ↔
      ∃ w : Fin 4 → K, w ≠ 0 ∧
        ∀ r s, r < s → w r * U r s = -(w s * U s r) := by
  obtain ⟨e, hfac⟩ := fourCoordinateVertex_supplied_presentation_square Z i U hdiag eRow hpoint
  exact suppliedFourTangent_intrinsic_weighted_iff _ U hdiag e hfac

theorem fourCoordinateVertex_supplied_intrinsic_fullBase_alternative
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (eRow : ∀ r, Z r ≅ Spec (.of (DualNumber K)))
    (hpoint : ∀ r, (eRow r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hdiag]) = i r ≫ quotientProjMap ⊥)
    (hskew : ∀ r s, U r s = -U s r)
    (hnonzero : ∀ r s, r ≠ s → U r s ≠ 0) :
    QuarticNet.IntrinsicFullBaseEmbeddedAlternative
      (Sigma.desc (fun r => i r ≫ quotientProjMap ⊥)) := by
  obtain ⟨e, hfac⟩ := fourCoordinateVertex_supplied_presentation_square Z i U hdiag eRow hpoint
  exact suppliedFourTangent_intrinsic_fullBase_alternative _ U hdiag e hfac hskew hnonzero

end PfaffianDescent

import PfaffianDescent.FourCoordinateVertexActualEpsilonRows
import PfaffianDescent.FourCoordinateVertexSuppliedLiteralComponent
import PfaffianDescent.CoordinateVertexSuppliedEpsilonComparison

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

/-- Derive a single actual presentation and BOTH literal conclusions for
it. The base-locus implication uses precisely the later lemma's supplied
skew/full-support assumptions. The weighted IFF itself has no such input. -/
theorem fourCoordinateVertex_actual_exists_literal_presentation
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
          ∀ r s, r < s → w r * U r s = -(w s * U s r)) ∧
      ((∀ r s, U r s = -U s r) → (∀ r s, r ≠ s → U r s ≠ 0) →
        QuarticNet.IntrinsicFullBaseEmbeddedAlternative
          (Sigma.desc (fun r => i r ≫ quotientProjMap ⊥))) := by
  obtain ⟨U, eRow, hdiag, hRows, hpoint⟩ :=
    fourCoordinateVertex_actual_exists_epsilon_presentations Z i hSupport hZ
  obtain ⟨e, hfac⟩ := fourCoordinateVertex_supplied_presentation_square Z i U hdiag eRow hpoint
  refine ⟨U, e, hdiag, hRows, hfac,
    suppliedFourTangent_intrinsic_weighted_iff _ U hdiag e hfac, ?_⟩
  intro hskew hnonzero
  exact suppliedFourTangent_intrinsic_fullBase_alternative _ U hdiag e hfac hskew hnonzero

/-- Starting with actual components only, derive a reference epsilon
presentation and compare EVERY other supplied actual presentation to it.
No canonical skew/full-support assumption is imposed. The arbitrary V's
weighted IFF is derived, and V's literal later-lemma hypotheses imply the
base alternative for the same original components. -/
theorem fourCoordinateVertex_actual_exists_choice_independent_literal_presentation
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [∀ r, IsClosedImmersion (i r)] [∀ r, IsFinite (i r ≫ toBase ⊥)]
    (hSupport : ∀ r, Set.range (i r) = {coordinateVertex (K := K) r})
    (hZ : ∀ r, AllCharacteristics.finiteSchemeRank (i r ≫ toBase ⊥) = 2) :
    ∃ (U : Fin 4 → Fin 4 → K)
      (eOne : ∀ r, Z r ≅ Spec (.of (DualNumber K))) (hUdiag : ∀ r, U r r = 0),
      (∀ r, U r ≠ 0) ∧
      (∀ r, (eOne r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hUdiag]) = i r ≫ quotientProjMap ⊥) ∧
      ∀ (V : Fin 4 → Fin 4 → K) (hVdiag : ∀ r, V r r = 0)
        (eTwo : ∀ r, Z r ≅ Spec (.of (DualNumber K))),
        (∀ r, (eTwo r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
          (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
            TrivSqZeroExt.inr (V r s)) r
          (by simp [coordinateVertexCoordinates, hVdiag]) = i r ≫ quotientProjMap ⊥) →
        ∃ (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0),
          V = QuarticNet.rescaleTangentDirections l U ∧
          (∀ r, (eTwo r).hom ≫ Spec.map (CommRingCat.ofHom
            (QuarticNet.dualNumberRescaleEquiv (l r) (hl r)).toRingHom) = (eOne r).hom) ∧
          (3 ≤ finrank K (intrinsicFullQuadraticSystem
            (Sigma.desc (fun r => i r ≫ quotientProjMap ⊥))) ↔
            ∃ w : Fin 4 → K, w ≠ 0 ∧
              ∀ r s, r < s → w r * V r s = -(w s * V s r)) ∧
          ((∀ r s, V r s = -V s r) → (∀ r s, r ≠ s → V r s ≠ 0) →
            QuarticNet.IntrinsicFullBaseEmbeddedAlternative
              (Sigma.desc (fun r => i r ≫ quotientProjMap ⊥))) := by
  obtain ⟨U, eOne, hUdiag, hRows, hOne⟩ :=
    fourCoordinateVertex_actual_exists_epsilon_presentations Z i hSupport hZ
  refine ⟨U, eOne, hUdiag, hRows, hOne, ?_⟩
  intro V hVdiag eTwo hTwo
  obtain ⟨l, hl, hV, hSource⟩ := fourCoordinateVertex_supplied_presentations_rescale
    Z i U V hUdiag hVdiag eOne eTwo hOne hTwo
  refine ⟨l, hl, hV, hSource,
    fourCoordinateVertex_supplied_intrinsic_weighted_iff Z i V hVdiag eTwo hTwo, ?_⟩
  intro hskew hnonzero
  exact fourCoordinateVertex_supplied_intrinsic_fullBase_alternative
    Z i V hVdiag eTwo hTwo hskew hnonzero

end PfaffianDescent

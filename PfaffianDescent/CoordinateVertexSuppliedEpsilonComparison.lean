import PfaffianDescent.CoordinateVertexSingleEpsilonRescale

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

/-- Row labels are preserved: independent choices on the same four actual
components differ by nonzero row scalings, not by a permutation or a new jet. -/
theorem fourCoordinateVertex_supplied_presentations_rescale
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    (U V : Fin 4 → Fin 4 → K)
    (hUdiag : ∀ r, U r r = 0) (hVdiag : ∀ r, V r r = 0)
    (eOne eTwo : ∀ r, Z r ≅ Spec (.of (DualNumber K)))
    (hOne : ∀ r, (eOne r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
      (fun s => inl (coordinateVertexCoordinates (K := K) r s) + inr (U r s)) r
      (by simp [coordinateVertexCoordinates, hUdiag]) = i r ≫ quotientProjMap ⊥)
    (hTwo : ∀ r, (eTwo r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
      (fun s => inl (coordinateVertexCoordinates (K := K) r s) + inr (V r s)) r
      (by simp [coordinateVertexCoordinates, hVdiag]) = i r ≫ quotientProjMap ⊥) :
    ∃ (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0),
      V = QuarticNet.rescaleTangentDirections l U ∧
      ∀ r, (eTwo r).hom ≫ Spec.map (CommRingCat.ofHom
        (QuarticNet.dualNumberRescaleEquiv (l r) (hl r)).toRingHom) = (eOne r).hom := by
  classical
  have hEach (r : Fin 4) := coordinateVertex_supplied_epsilon_presentations_rescale
    (i r ≫ quotientProjMap ⊥) r (U r) (V r) (hUdiag r) (hVdiag r)
    (eOne r) (eTwo r) (hOne r) (hTwo r)
  choose l hl hCoordinates hSource using hEach
  refine ⟨l, hl, ?_, hSource⟩
  funext r s
  exact hCoordinates r s

end PfaffianDescent

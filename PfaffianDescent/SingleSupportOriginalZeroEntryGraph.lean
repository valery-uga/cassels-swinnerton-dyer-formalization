import PfaffianDescent.ConjugateQuarticZeroEntrySupportGraph
import PfaffianDescent.SingleSupportIntrinsicSkewTangent
import PfaffianDescent.AmbientTensorNormalizedChartSquare

/-! Source-only, UNVERIFIED.  Literal graph conclusion for the tangent
matrix extracted from the SAME originally supplied rank-eight Z.  Original
Gamma(Z), its exact original embedding and the actual chart permutation
remain in the result.  No coordinate/covariance/graph-shape premise is added. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem singleSupport_originalZ_zero_entry_tangent_graph
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase I).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition I ((scheme I).fromSpecResidueField P.1))
    (hdim : 3 ≤ finrank k (intrinsicFullQuadraticSystem (i ≫ quotientProjMap I))) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    letI := AllCharacteristics.pointAlgebra (toBase I) P.1
    (AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8) →
    ∃ (j : Fin 4) (x : Fin 4 → Γ(Z, ⊤)) (hxj : x j = 1)
      (eA : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme I).residueField P.1))
      (b : Basis (Fin 4) k ((scheme I).residueField P.1))
      (v : Fin 4 → (scheme I).residueField P.1) (pi : Equiv.Perm (Fin 4))
      (full : Fin 4 ≃ ((scheme I).residueField P.1 →ₐ[k] AlgebraicClosure k))
      (l : Fin 4 → AlgebraicClosure k),
      pi 0 = j ∧ b 0 = 1 ∧ v 0 = 0 ∧ v ≠ 0 ∧ (∀ r, l r ≠ 0) ∧
      (∀ r, eA (x (pi r)) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r)) ∧
      ambientNormalizedCoordinateChartPoint x j hxj = Z.isoSpec.inv ≫ i ≫ quotientProjMap I ∧
      let U := QuarticNet.conjugateTangentMatrix full b v
        (QuarticNet.conjugate_basis_span b full)
      (∀ r s, l r * U r s = -(l s * U s r)) ∧
      ((∃ r s, r ≠ s ∧ QuarticNet.rescaleTangentDirections l U r s = 0) →
        QuarticNet.ZeroEntryTangentSupportClassification
          (QuarticNet.rescaleTangentDirections l U)) := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  intro hZ
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  obtain ⟨j, g, x, eA, b, v, pi, full, hxj, hgen, hgb, hb, hv, hvne, hpi,
    hcoords, hpoint, hx, hspan, hactual, hgroundKernel, hnrows, l, hl,
    hskew, hrescaledKernel⟩ :=
    singleSupport_intrinsic_quadratics_actual_skew_tangents
      I i P hSupport hP hGeom hdim hZ
  have hq0 : ambientNormalizedCoordinateChartPoint x j hxj =
      Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
    have h := ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hgb
    have hcoordsEq : (fun r => g (chartCoordinate I j r)) = x :=
      funext (fun r => (hcoords r).symm)
    rw [hcoordsEq] at h
    rw [h, ← Category.assoc, hpoint, Category.assoc]
  refine ⟨j, x, hxj, eA, b, v, pi, full, l, hpi, hb, hv, hvne, hl,
    hx, hq0, hskew, ?_⟩
  intro hmissing
  exact QuarticNet.conjugateQuartic_zero_entry_support_graph
    full b v (QuarticNet.conjugate_basis_span b full) l hl hskew hb hv hvne hmissing

end PfaffianDescent

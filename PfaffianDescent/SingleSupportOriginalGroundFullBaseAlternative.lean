import PfaffianDescent.ActualQuarticOriginalGroundFullBaseAlternative
import PfaffianDescent.SingleSupportIntrinsicSkewTangent
import PfaffianDescent.IntrinsicOriginalGroundFullBaseGeometry

/-! The ground-field full-base alternative for the ORIGINAL supplied Z.
All actual chart, dual-algebra, tangent, skew-rescaling, and full-base descent
data are obtained internally. The six-entry nondegenerate branch is explicit
in the conclusion; zero off-diagonal entries are not silently excluded. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem singleSupport_original_ground_fullBase_nondegenerate_branch
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
      pi 0 = j ∧ b 0 = 1 ∧ v 0 = 0 ∧ (∀ r, l r ≠ 0) ∧
      (∀ r, eA (x (pi r)) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r)) ∧
      ambientNormalizedCoordinateChartPoint x j hxj = Z.isoSpec.inv ≫ i ≫ quotientProjMap I ∧
      let U := QuarticNet.conjugateTangentMatrix full b v
        (QuarticNet.conjugate_basis_span b full)
      (∀ r s, l r * U r s = -(l s * U s r)) ∧
      ((∀ r s, r ≠ s → U r s ≠ 0) →
        IntrinsicOriginalGroundFullBaseAlternative (i ≫ quotientProjMap I)) := by
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
  let q0 := ambientNormalizedCoordinateChartPoint x j hxj
  let a := i ≫ quotientProjMap I
  have hq0 : q0 = Z.isoSpec.inv ≫ a := by
    have h := ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hgb
    have hcoordsEq : (fun r => g (chartCoordinate I j r)) = x :=
      funext (fun r => (hcoords r).symm)
    rw [hcoordsEq] at h
    rw [h, ← Category.assoc, hpoint, Category.assoc]
  refine ⟨j, x, hxj, eA, b, v, pi, full, l, hpi, hb, hv, hl, hx, hq0, hskew, ?_⟩
  intro hnonzero
  have hAlt : QuarticNet.IntrinsicFullBaseEmbeddedAlternative q0 :=
    QuarticNet.actualQuarticOriginalGround_fullBase_embedded_alternative
      eA x hgen j hxj pi hpi b v hx hb hv full l hl hskew hnonzero
  rw [hq0] at hAlt
  have hBa : intrinsicFullQuadraticBaseIdeal (Z.isoSpec.inv ≫ a) =
      intrinsicFullQuadraticBaseIdeal a := by
    apply HomogeneousIdeal.toIdeal_injective
    change Ideal.span (intrinsicFullQuadraticSystem (Z.isoSpec.inv ≫ a) : Set _) =
      Ideal.span (intrinsicFullQuadraticSystem a : Set _)
    rw [intrinsicFullQuadraticSystem_comp_isIso]
  unfold QuarticNet.IntrinsicFullBaseEmbeddedAlternative at hAlt
  unfold IntrinsicOriginalGroundFullBaseAlternative
  rw [hBa] at hAlt
  rcases hAlt with ⟨f, hf, hfac⟩ | hTwisted
  · letI := hf
    exact Or.inl ⟨Z.isoSpec.hom ≫ f, inferInstance, by
      rw [Category.assoc, hfac, Iso.hom_inv_id_assoc]⟩
  · exact Or.inr (intrinsicOriginalTwistedFullBase_geometry a hTwisted)

end PfaffianDescent

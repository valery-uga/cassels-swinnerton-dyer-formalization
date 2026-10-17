import PfaffianDescent.ActualQuarticSkewQuadraticDimensionDescent
import PfaffianDescent.SingleSupportOriginalOrderDualChartData
import PfaffianDescent.ActualP3IdealQuadraticGlobalBase
import PfaffianDescent.IntrinsicQuadraticCoordinatePermutation
import PfaffianDescent.ActualSuppliedChartTensorEmbedding

/-! SOURCE ONLY, UNVERIFIED. A converse on the SAME original finite closed
rank-eight Z and its actual original-order dual/ambient presentation. Actual
H0 and kernel/chart comparisons are proved internally. No new frame is
identified with an arbitrary already-supplied graph by this declaration. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Ordinary actual chart/dual data and skew weights, WITHOUT H0 or a
kernel comparison premise, imply genuine H0 >=3 for the original immersion.
The original support/degree/general-position/rank hypotheses remain explicit.
Presentation arguments occur universally in the conclusion. -/
theorem singleSupport_original_skew_presentation_actual_HZero_three
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase I).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition I ((scheme I).fromSpecResidueField P.1)) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    letI := AllCharacteristics.pointAlgebra (toBase I) P.1
    (AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8) →
    ∀ (j : Fin 4) (g : ChartRing I j →+* Γ(Z, ⊤)) (x : Fin 4 → Γ(Z, ⊤))
      (eA : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme I).residueField P.1))
      (b : Basis (Fin 4) k ((scheme I).residueField P.1))
      (v : Fin 4 → (scheme I).residueField P.1)
      (full : Fin 4 ≃ ((scheme I).residueField P.1 →ₐ[k] AlgebraicClosure k)),
      x j = 1 → g.comp (chartBaseMap I j) = algebraMap k Γ(Z, ⊤) →
      (∀ r, x r = g (chartCoordinate I j r)) →
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = Z.isoSpec.inv ≫ i →
      (∀ r, eA (x r) = inl (b r) + inr (v r)) →
      ∀ (l : Fin 4 → AlgebraicClosure k), (∀ r, l r ≠ 0) →
      (let U := QuarticNet.conjugateTangentMatrix full b v
        (QuarticNet.conjugate_basis_span b full);
        ∀ r s, l r * U r s = -(l s * U s r)) →
      3 ≤ finrank k (ActualP3IdealQuadraticHZero (i ≫ quotientProjMap I)) := by
  classical
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  intro hZ j g x eA b v full hxj hbase hxg hpoint hcoords l hl hskew
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  have hEval : 3 ≤ finrank k (homogeneousVanishingPolynomialSubmodule (K := k) x 2) :=
    QuarticNet.actualQuarticSkew_ground_quadratic_finrank_three
      eA x b v hcoords full l hl hskew
  let q0 := ambientNormalizedCoordinateChartPoint (F := k) x j hxj
  have hq0 : q0 = Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
    have h := ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hbase
    have hx : (fun r => g (chartCoordinate I j r)) = x :=
      funext (fun r => (hxg r).symm)
    rw [hx] at h
    change ambientNormalizedCoordinateChartPoint x j hxj = _
    rw [h, ← Category.assoc, hpoint, Category.assoc]
  have hW : intrinsicFullQuadraticSystem (i ≫ quotientProjMap I) =
      homogeneousVanishingPolynomialSubmodule (K := k) x 2 := by
    calc
      _ = intrinsicFullQuadraticSystem q0 := by
        rw [hq0, intrinsicFullQuadraticSystem_comp_isIso]
      _ = _ := ambientNormalizedCoordinateChartPoint_intrinsicQuadratics x j hxj
  change 3 ≤ finrank k (SchemeModuleGlobalSectionsOver
    (ambientToBase (R := k) (σ := Fin 4))
    (closedImmersionIdealTwist (i ≫ quotientProjMap I)
      (positiveSheafOfModules (homogeneousSubmodule (Fin 4) k) 2)))
  rw [p3ActualIdealQuadratic_finrank_eq_intrinsic (i ≫ quotientProjMap I), hW]
  exact hEval

/-- Extract actual original-order data WITHOUT H0, and prove the conditional
skew=>H0 converse for its SAME matrix. This does not assert skew weights exist
for every rank-eight jet, nor compare a new extraction with an old graph. -/
theorem singleSupport_original_order_data_skew_implies_actual_HZero_three
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase I).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition I ((scheme I).fromSpecResidueField P.1)) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    letI := AllCharacteristics.pointAlgebra (toBase I) P.1
    (AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8) →
    ∃ (j : Fin 4) (g : ChartRing I j →+* Γ(Z, ⊤)) (x : Fin 4 → Γ(Z, ⊤))
      (eA : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme I).residueField P.1))
      (b : Basis (Fin 4) k ((scheme I).residueField P.1))
      (v : Fin 4 → (scheme I).residueField P.1)
      (full : Fin 4 ≃ ((scheme I).residueField P.1 →ₐ[k] AlgebraicClosure k)),
      x j = 1 ∧ Function.Surjective (aeval (R := k) x) ∧
      g.comp (chartBaseMap I j) = algebraMap k Γ(Z, ⊤) ∧
      b j = 1 ∧ v j = 0 ∧ v ≠ 0 ∧
      (∀ r, x r = g (chartCoordinate I j r)) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = Z.isoSpec.inv ≫ i ∧
      (∀ r, eA (x r) = inl (b r) + inr (v r)) ∧
      ∀ (l : Fin 4 → AlgebraicClosure k), (∀ r, l r ≠ 0) →
      (let U := QuarticNet.conjugateTangentMatrix full b v
        (QuarticNet.conjugate_basis_span b full);
        ∀ r s, l r * U r s = -(l s * U s r)) →
      3 ≤ finrank k (ActualP3IdealQuadraticHZero (i ≫ quotientProjMap I)) := by
  classical
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  intro hZ
  obtain ⟨j, g, x, eA, b, v, full, hxj, hgen, hbase, hb, hvj, hv, hxg, hpoint, hcoords⟩ :=
    singleSupport_actual_original_order_dual_chart_data I i P hSupport hP hGeom hZ
  refine ⟨j, g, x, eA, b, v, full, hxj, hgen, hbase, hb, hvj, hv, hxg, hpoint, hcoords, ?_⟩
  intro l hl hskew
  exact singleSupport_original_skew_presentation_actual_HZero_three
    I i P hSupport hP hGeom hZ j g x eA b v full hxj hbase hxg hpoint hcoords l hl hskew

end PfaffianDescent

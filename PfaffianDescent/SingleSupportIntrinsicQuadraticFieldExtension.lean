import PfaffianDescent.NormalizedIntrinsicQuadraticFieldExtension
import PfaffianDescent.SingleSupportActualTensorAmbientSquare
import PfaffianDescent.SingleSupportIntrinsicQuadraticRestriction

/-! The full intrinsic quadratic system of the TRUE original singleton-
support finite closed scheme commutes with every field extension. Its chart,
coordinate algebra, and actual two projection squares are derived internally.
There is no perfectness, degree-four, dual-algebra or geometric certificate. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem singleSupport_intrinsicFullQuadratic_fieldExtension
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1}) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
    ∃ (j : Fin 4) (x : Fin 4 → Γ(Z, ⊤)) (hx : x j = 1),
      let e := finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase I)
      let q := e.hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hx)
      q ≫ ambientCoefficientMap (algebraMap k K) =
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (i ≫ toBase I) ≫ i ≫ quotientProjMap I ∧
      q ≫ ambientToBase (R := K) =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase I) ∧
      intrinsicFullQuadraticSystem q = homogeneousPolynomialCoefficientSpan (K := K)
        (intrinsicFullQuadraticSystem (i ≫ quotientProjMap I)) ∧
      intrinsicFullQuadraticBaseIdeal q = HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom (algebraMap k K))
        (intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I)) ∧
      finrank K (intrinsicFullQuadraticSystem q) =
        finrank k (intrinsicFullQuadraticSystem (i ≫ quotientProjMap I)) := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  obtain ⟨j, g, x, hx, hgen, hgb, hcoords, hle, hpoint⟩ :=
    singleSupport_intrinsic_quadratics_actual_restriction I i P hSupport
  let q0 := ambientNormalizedCoordinateChartPoint (F := k) x j hx
  have hq0 : q0 = Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
    have h := ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hgb
    have hc : (fun r => g (chartCoordinate I j r)) = x :=
      funext (fun r => (hcoords r).symm)
    rw [hc] at h
    change ambientNormalizedCoordinateChartPoint x j hx = _
    rw [h, ← Category.assoc, hpoint, Category.assoc]
  have hW0 : intrinsicFullQuadraticSystem q0 =
      intrinsicFullQuadraticSystem (i ≫ quotientProjMap I) := by
    rw [hq0, intrinsicFullQuadraticSystem_comp_isIso]
  have hB0 : intrinsicFullQuadraticBaseIdeal q0 =
      intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I) := by
    unfold intrinsicFullQuadraticBaseIdeal
    rw [hW0]
  let e := finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase I)
  let qt := ambientNormalizedCoordinateChartPoint (F := K)
    (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hx)
  let q := e.hom ≫ qt
  have hW : intrinsicFullQuadraticSystem q =
      homogeneousPolynomialCoefficientSpan (K := K)
        (intrinsicFullQuadraticSystem (i ≫ quotientProjMap I)) := by
    rw [intrinsicFullQuadraticSystem_comp_isIso]
    rw [ambientNormalizedCoordinateChartPoint_intrinsicQuadratics_fieldExtension, hW0]
  have hB : intrinsicFullQuadraticBaseIdeal q = HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom (algebraMap k K))
        (intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I)) := by
    have heq : intrinsicFullQuadraticBaseIdeal q = intrinsicFullQuadraticBaseIdeal qt := by
      unfold intrinsicFullQuadraticBaseIdeal
      rw [intrinsicFullQuadraticSystem_comp_isIso]
    rw [heq, ambientNormalizedCoordinateChartPoint_intrinsicFullBase_fieldExtension, hB0]
  refine ⟨j, x, hx, ?_, ?_, hW, hB, ?_⟩
  · change (e.hom ≫ qt) ≫ ambientCoefficientMap _ = _
    calc
      (e.hom ≫ qt) ≫ ambientCoefficientMap _ =
          e.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k]
              K ⊗[k] Γ(Z, ⊤)).toRingHom) ≫ q0 := by
        rw [Category.assoc, ambientNormalizedCoordinateChartPoint_tensor_coefficients]
      _ = (e.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k]
              K ⊗[k] Γ(Z, ⊤)).toRingHom) ≫ Z.isoSpec.inv) ≫
          i ≫ quotientProjMap I := by rw [hq0]; simp only [Category.assoc]
      _ = _ := by rw [finiteSchemeActualFieldBaseChangeIso_hom_toOriginal]
  · rw [Category.assoc, ambientNormalizedCoordinateChartPoint_toBase]
    exact finiteSchemeActualFieldBaseChangeIso_hom_toField (K := K) (i ≫ toBase I)
  · rw [intrinsicFullQuadraticSystem_comp_isIso,
      ambientNormalizedCoordinateChartPoint_intrinsicQuadratics_fieldExtension_finrank, hW0]

end PfaffianDescent

import PfaffianDescent.SingleSupportIntrinsicQuadraticFieldExtension
import PfaffianDescent.ActualTensorCoordinateFiniteEmbedding
import PfaffianDescent.IntrinsicFullQuadraticBaseDimensionInfinite
import Mathlib.FieldTheory.RatFunc.Basic

/-! Dimension three over EVERY ground field for an actual normalized finite
rank-eight point, hence for any original singleton-support finite immersion.
No ground finite-triple/dimension/base-change certificate is assumed.
This does not assert that arbitrary finite subschemes fit a ground chart. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem normalizedIntrinsicFullQuadraticSystem_finrank_three_of_finite_base
    (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1)
    (hgen : Function.Surjective (aeval (R := k) x))
    (hA : finrank k A = 8)
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
      (ambientNormalizedCoordinateChartPoint x j hx)))] :
    finrank k (intrinsicFullQuadraticSystem
      (ambientNormalizedCoordinateChartPoint x j hx)) = 3 := by
  let K := RatFunc k
  letI : Infinite K :=
    Infinite.of_injective (algebraMap (Polynomial k) (RatFunc k))
      (RatFunc.algebraMap_injective k)
  let y : Fin 4 → K ⊗[k] A := fun r => (1 : K) ⊗ₜ[k] x r
  have hy : y j = 1 := tensor_coordinate_eq_one x j hx
  let qt := ambientNormalizedCoordinateChartPoint (F := K) y j hy
  let eB := normalizedIntrinsicFullQuadraticBaseFieldExtensionIso (K := K) x j hx
  letI : IsFinite (toBase (intrinsicFullQuadraticBaseIdeal qt)) := by
    rw [← normalizedIntrinsicFullQuadraticBaseFieldExtensionIso_hom_toField
      (K := K) x j hx]
    infer_instance
  letI : IsClosedImmersion qt :=
    ambientNormalizedCoordinateChartPoint_isClosedImmersion y j hy
      (tensorCoordinates_aeval_surjective x hgen)
  letI : IsFinite (qt ≫ ambientToBase) :=
    ambientNormalizedCoordinateChartPoint_finite_toBase y j hy
  letI : Module.Free k A := Module.Free.of_divisionRing k A
  have hAnew : finrank K (K ⊗[k] A) = 8 :=
    (Module.finrank_baseChange (R := K) (S := k) (M' := A)).trans hA
  have hZ : AllCharacteristics.finiteSchemeRank (qt ≫ ambientToBase) = 8 :=
    (ambientNormalizedCoordinateChartPoint_finiteSchemeRank y j hy).trans hAnew
  have hd := intrinsicFullQuadraticSystem_finrank_eq_three_of_finite_base qt hZ
  have hdim := ambientNormalizedCoordinateChartPoint_intrinsicQuadratics_fieldExtension_finrank
    (K := K) x j hx
  exact hdim.symm.trans hd

/-- The dimension statement is attached to the SAME original supplied Z;
its chart and all coefficient-extension comparisons are internal. -/
theorem singleSupport_intrinsicFullQuadraticSystem_finrank_three_of_finite_base
    {k : Type u} [Field k]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8)
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal (i ≫ quotientProjMap I)))] :
    finrank k (intrinsicFullQuadraticSystem (i ≫ quotientProjMap I)) = 3 := by
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
  letI : IsFinite (toBase (intrinsicFullQuadraticBaseIdeal q0)) := by
    rw [hB0]
    infer_instance
  have hA : finrank k Γ(Z, ⊤) = 8 :=
    (finiteSchemeCoefficient_finrank (i ≫ toBase I)).trans hZ
  rw [← hW0]
  exact normalizedIntrinsicFullQuadraticSystem_finrank_three_of_finite_base x j hx hgen hA

end PfaffianDescent

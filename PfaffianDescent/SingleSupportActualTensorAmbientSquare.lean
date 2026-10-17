import PfaffianDescent.AmbientTensorNormalizedChartSquare
import PfaffianDescent.SingleSupportProjectiveCoordinates
import PfaffianDescent.SingleSupportGeometricSchemeSplitting

/-! Actual ambient normalized coordinates on the field base change of the
ORIGINAL supplied scheme. Both projections are proved internally using its
true affine reconstruction and actual original quotient chart immersion. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The true tensor presentation also retains the extension-field leg. -/
theorem finiteSchemeActualFieldBaseChangeIso_hom_toField
    {Z : Scheme.{u}} (t : Z ⟶ Spec (.of k)) [IsFinite t] :
    letI := finiteSchemeCoefficientAlgebra t
    (finiteSchemeActualFieldBaseChangeIso (K := K) t).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] Γ(Z, ⊤)))) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) t := by
  letI := finiteSchemeCoefficientAlgebra t
  dsimp only [finiteSchemeActualFieldBaseChangeIso]
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  erw [pullbackSpecIso_hom_fst]
  unfold pullback.map
  rw [pullback.lift_fst]
  simp

/-- From the literal actual support and finite closed immersion, obtain
normalized tensor coordinates satisfying both ambient base-change squares.
No comparison with the original embedding is supplied as an input. -/
theorem singleSupport_actual_projective_tensor_chart_square
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1}) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    ∃ (j : Fin 4) (x : Fin 4 → Γ(Z, ⊤)) (hx : x j = 1),
      let e := finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase I)
      let q := ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hx)
      (e.hom ≫ q) ≫ ambientCoefficientMap (algebraMap k K) =
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase I) ≫
          i ≫ quotientProjMap I ∧
      (e.hom ≫ q) ≫ ambientToBase (R := K) =
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase I) := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  obtain ⟨j, g, hgs, hbase, hpoint⟩ := singleSupport_projective_actual_chart I i P hSupport
  let x : Fin 4 → Γ(Z, ⊤) := fun r => g (chartCoordinate I j r)
  have hx : x j = 1 := by simp only [x, chartCoordinate_self, map_one]
  let e := finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase I)
  let q := ambientNormalizedCoordinateChartPoint (F := K)
    (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hx)
  have hqA : ambientNormalizedCoordinateChartPoint x j hx =
      Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
    rw [ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hbase]
    rw [← Category.assoc, hpoint, Category.assoc]
  refine ⟨j, x, hx, ?_, ?_⟩
  · change (e.hom ≫ q) ≫ ambientCoefficientMap (algebraMap k K) = _
    calc
      (e.hom ≫ q) ≫ ambientCoefficientMap (algebraMap k K) =
          e.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k]
              K ⊗[k] Γ(Z, ⊤)).toRingHom) ≫
            ambientNormalizedCoordinateChartPoint x j hx := by
        rw [Category.assoc]
        exact congrArg (fun f => e.hom ≫ f)
          (ambientNormalizedCoordinateChartPoint_tensor_coefficients (K := K) x j hx)
      _ = (e.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k]
              K ⊗[k] Γ(Z, ⊤)).toRingHom) ≫ Z.isoSpec.inv) ≫
          i ≫ quotientProjMap I := by rw [hqA]; simp only [Category.assoc]
      _ = _ := by rw [finiteSchemeActualFieldBaseChangeIso_hom_toOriginal]
  · change (e.hom ≫ q) ≫ ambientToBase (R := K) = _
    rw [Category.assoc, ambientNormalizedCoordinateChartPoint_toBase]
    exact finiteSchemeActualFieldBaseChangeIso_hom_toField (K := K) (i ≫ toBase I)

end PfaffianDescent

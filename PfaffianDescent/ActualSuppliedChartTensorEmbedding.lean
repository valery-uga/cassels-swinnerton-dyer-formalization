import PfaffianDescent.SingleSupportActualTensorAmbientSquare

/-! SOURCE ONLY, UNVERIFIED. Reuse the SAME chart already selected by actual
supplied-Z extraction. This helper has ordinary chart-description arguments;
the literal geometric caller derives each of them internally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actualSuppliedChart_tensor_ambient_squares
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsFinite (i ≫ toBase I)]
    (j : Fin 4) (g : ChartRing I j →+* Γ(Z, ⊤))
    (hbase : letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
      g.comp (chartBaseMap I j) = algebraMap k Γ(Z, ⊤))
    (hpoint : letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = Z.isoSpec.inv ≫ i)
    (x : Fin 4 → Γ(Z, ⊤)) (hxg : ∀ r, x r = g (chartCoordinate I j r))
    (hxj : x j = 1) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    let Q := (finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase I)).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
    Q ≫ ambientCoefficientMap (algebraMap k K) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase I) ≫
        i ≫ quotientProjMap I ∧
    Q ≫ ambientToBase (R := K) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase I) := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  let e := finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase I)
  let q := ambientNormalizedCoordinateChartPoint (F := K)
    (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hxj)
  have hx : x = fun r => g (chartCoordinate I j r) := funext hxg
  have hqA : ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
      Z.isoSpec.inv ≫ i ≫ quotientProjMap I := by
    have h := ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hbase
    have hOriginalChart : ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
        Spec.map (CommRingCat.ofHom g) ≫ chartι I j ≫ quotientProjMap I := by
      simpa only [← hx] using h
    exact hOriginalChart.trans (by rw [← Category.assoc, hpoint, Category.assoc])
  constructor
  · change (e.hom ≫ q) ≫ ambientCoefficientMap (algebraMap k K) = _
    calc
      (e.hom ≫ q) ≫ ambientCoefficientMap (algebraMap k K) =
          e.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k]
              K ⊗[k] Γ(Z, ⊤)).toRingHom) ≫
            ambientNormalizedCoordinateChartPoint (F := k) x j hxj := by
        rw [Category.assoc]
        exact congrArg (fun f => e.hom ≫ f)
          (ambientNormalizedCoordinateChartPoint_tensor_coefficients (K := K) x j hxj)
      _ = (e.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k]
              K ⊗[k] Γ(Z, ⊤)).toRingHom) ≫ Z.isoSpec.inv) ≫
          i ≫ quotientProjMap I := by rw [hqA]; simp only [Category.assoc]
      _ = _ := by rw [finiteSchemeActualFieldBaseChangeIso_hom_toOriginal]
  · change (e.hom ≫ q) ≫ ambientToBase (R := K) = _
    rw [Category.assoc, ambientNormalizedCoordinateChartPoint_toBase]
    exact finiteSchemeActualFieldBaseChangeIso_hom_toField (K := K) (i ≫ toBase I)

end PfaffianDescent

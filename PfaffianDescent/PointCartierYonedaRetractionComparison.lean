import PfaffianDescent.PointCartierYonedaUnitLift
import PfaffianDescent.PointCartierYonedaSurfaceKoszul

/-! # The explicit ambient-to-surface Koszul comparison

The degree-one and degree-two maps satisfy the augmentation and relation
squares of the actual two-parameter surface Koszul resolution.
-/

noncomputable section

namespace PfaffianDescent

variable {R : Type*} [CommRing R]

theorem pointCartierYonedaUnitLift_normalized (v : Rˣ) (b c : R) (x : R × R × R) :
    pointCartierYonedaUnitLift v b c x =
      (v⁻¹ : Rˣ) * c * x.1 - (v⁻¹ : Rˣ) * b * x.2.1 + x.2.2 := by
  rw [pointCartierYonedaUnitLift_apply]
  calc
    (v⁻¹ : Rˣ) * (c * x.1 - b * x.2.1 + (v : R) * x.2.2) =
      (v⁻¹ : Rˣ) * c * x.1 - (v⁻¹ : Rˣ) * b * x.2.1 +
        ((v⁻¹ : Rˣ) * (v : R)) * x.2.2 := by ring
    _ = _ := by rw [Units.inv_mul, one_mul]

theorem pointCartierYonedaUnitRetraction_relation
    (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) :
    let q := Ideal.Quotient.mk (Ideal.span {p})
    q f + q g * q b * q (v⁻¹ : Rˣ) + q h * q c * q (v⁻¹ : Rˣ) = 0 := by
  dsimp
  let q := Ideal.Quotient.mk (Ideal.span {p})
  have heq' : q (f * (v : R) + g * b + h * c) = 0 := by
    rw [← heq]
    exact Ideal.Quotient.mk_singleton_self p
  have hu : q (v : R) * q (v⁻¹ : Rˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only [map_add, map_mul] at heq'
  linear_combination q (v⁻¹ : Rˣ) * heq' - q f * hu

/-- The comparison commutes with the maps to the parameter ideal. -/
theorem pointCartierYonedaUnitRetraction_last
    (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) (x : R × R × R) :
    let q := Ideal.Quotient.mk (Ideal.span {p})
    localKoszulGeneratorMap (q g) (q h) (pointCartierYonedaUnitRetractionOne p v b c x) =
      q (threeGeneratorLast f g h x) := by
  dsimp only
  have hrel := pointCartierYonedaUnitRetraction_relation f g h p v b c heq
  simp only [pointCartierYonedaUnitRetractionOne, pointCartierYonedaUnitRetractionOneLift,
    localKoszulGeneratorMap, threeGeneratorLast, LinearMap.comp_apply, LinearMap.prodMap_apply,
    LinearMap.coe_mk, AddHom.coe_mk, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
    map_add, map_sub, map_mul]
  linear_combination -(Ideal.Quotient.mk (Ideal.span {p}) x.1) * hrel

/-- The relation square commutes, with the actual local Koszul orientation. -/
theorem pointCartierYonedaUnitRetraction_middle
    (f g h p : R) (v : Rˣ) (b c : R)
    (heq : p = f * (v : R) + g * b + h * c) (x : R × R × R) :
    let q := Ideal.Quotient.mk (Ideal.span {p})
    pointCartierYonedaUnitRetractionOne p v b c (threeGeneratorMiddle f g h x) =
      localKoszulRelationMap (q g) (q h) (pointCartierYonedaUnitCocycleMap p v b c x) := by
  dsimp only
  have hrel := pointCartierYonedaUnitRetraction_relation f g h p v b c heq
  have hnorm : pointCartierYonedaUnitCocycleMap p v b c x =
      Ideal.Quotient.mk (Ideal.span {p})
        ((v⁻¹ : Rˣ) * c * x.1 - (v⁻¹ : Rˣ) * b * x.2.1 + x.2.2) := by
    change Ideal.Quotient.mk (Ideal.span {p}) (pointCartierYonedaUnitLift v b c x) = _
    rw [pointCartierYonedaUnitLift_normalized]
  rw [hnorm]
  apply Prod.ext
  · change Ideal.Quotient.mk (Ideal.span {p})
      (f * x.1 - h * x.2.2 - b * (v⁻¹ : Rˣ) * (-g * x.1 - h * x.2.1)) =
        Ideal.Quotient.mk (Ideal.span {p})
          ((v⁻¹ : Rˣ) * c * x.1 - (v⁻¹ : Rˣ) * b * x.2.1 + x.2.2) *
            (-Ideal.Quotient.mk (Ideal.span {p}) h)
    simp only [map_add, map_sub, map_mul, map_neg]
    linear_combination (Ideal.Quotient.mk (Ideal.span {p}) x.1) * hrel
  · change Ideal.Quotient.mk (Ideal.span {p})
      (f * x.2.1 + g * x.2.2 - c * (v⁻¹ : Rˣ) * (-g * x.1 - h * x.2.1)) =
        Ideal.Quotient.mk (Ideal.span {p})
          ((v⁻¹ : Rˣ) * c * x.1 - (v⁻¹ : Rˣ) * b * x.2.1 + x.2.2) *
            Ideal.Quotient.mk (Ideal.span {p}) g
    simp only [map_add, map_sub, map_mul, map_neg]
    linear_combination (Ideal.Quotient.mk (Ideal.span {p}) x.2.1) * hrel

end PfaffianDescent

import PfaffianDescent.AmbientPointKoszulChartAlgebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Flat transport of the three-generator coordinate Koszul complex

Exactness of the explicit three-generator differential matrices survives
flat coefficient extension. This applies in particular to the actual
chart-to-stalk localization homomorphisms.
-/

noncomputable section
open TensorProduct
namespace PfaffianDescent

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Scalar extension of the explicit rank-three free module. -/
def ambientPointKoszul_tensorTriple :
    S ⊗[R] (R × R × R) ≃ₗ[R] (S × S × S) :=
  (TensorProduct.prodRight R R S R (R × R)).trans
    ((TensorProduct.rid R S).prodCongr
      ((TensorProduct.prodRight R R S R R).trans
        ((TensorProduct.rid R S).prodCongr (TensorProduct.rid R S))))

/-- Coordinates of a pure tensor under the scalar-extension identification. -/
theorem ambientPointKoszul_tensorTriple_tmul (s : S) (v : R × R × R) :
    ambientPointKoszul_tensorTriple R S (s ⊗ₜ[R] v) =
      (algebraMap R S v.1 * s, algebraMap R S v.2.1 * s, algebraMap R S v.2.2 * s) := by
  simp [ambientPointKoszul_tensorTriple, Algebra.smul_def]

private theorem first_ladder (f g h : R) :
    ((threeGeneratorFirst (algebraMap R S f) (algebraMap R S g) (algebraMap R S h)).restrictScalars R).comp
        (TensorProduct.rid R S).toLinearMap =
      (ambientPointKoszul_tensorTriple R S).toLinearMap.comp ((threeGeneratorFirst f g h).lTensor S) := by
  apply TensorProduct.ext'
  intro s r
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    LinearMap.lTensor_tmul, ambientPointKoszul_tensorTriple_tmul]
  ext <;> simp [threeGeneratorFirst, Algebra.smul_def] <;> ring

private theorem middle_ladder (f g h : R) :
    ((threeGeneratorMiddle (algebraMap R S f) (algebraMap R S g) (algebraMap R S h)).restrictScalars R).comp
        (ambientPointKoszul_tensorTriple R S).toLinearMap =
      (ambientPointKoszul_tensorTriple R S).toLinearMap.comp ((threeGeneratorMiddle f g h).lTensor S) := by
  apply TensorProduct.ext'
  intro s v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.lTensor_tmul, ambientPointKoszul_tensorTriple_tmul]
  ext <;> simp [threeGeneratorMiddle, Algebra.smul_def] <;> ring

private theorem last_ladder (f g h : R) :
    ((threeGeneratorLast (algebraMap R S f) (algebraMap R S g) (algebraMap R S h)).restrictScalars R).comp
        (ambientPointKoszul_tensorTriple R S).toLinearMap =
      (TensorProduct.rid R S).toLinearMap.comp ((threeGeneratorLast f g h).lTensor S) := by
  apply TensorProduct.ext'
  intro s v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    LinearMap.lTensor_tmul, ambientPointKoszul_tensorTriple_tmul]
  simp [threeGeneratorLast, Algebra.smul_def]
  ring

/-- Degree-two exactness survives flat scalar extension. -/
theorem ambientPointKoszul_flat_exact_middle [Module.Flat R S] (f g h : R)
    (hex : LinearMap.range (threeGeneratorFirst f g h) =
      LinearMap.ker (threeGeneratorMiddle f g h)) :
    LinearMap.range (threeGeneratorFirst (algebraMap R S f) (algebraMap R S g) (algebraMap R S h)) =
      LinearMap.ker (threeGeneratorMiddle (algebraMap R S f) (algebraMap R S g) (algebraMap R S h)) := by
  have ht : Function.Exact ((threeGeneratorFirst f g h).lTensor S)
      ((threeGeneratorMiddle f g h).lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr hex.symm)
  have hexact := Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.rid R S) (e₂ := ambientPointKoszul_tensorTriple R S)
    (e₃ := ambientPointKoszul_tensorTriple R S)
    (first_ladder R S f g h) (middle_ladder R S f g h) ht
  have h' : Function.Exact
      (threeGeneratorFirst (algebraMap R S f) (algebraMap R S g) (algebraMap R S h))
      (threeGeneratorMiddle (algebraMap R S f) (algebraMap R S g) (algebraMap R S h)) := hexact
  exact (LinearMap.exact_iff.mp h').symm

/-- Degree-one exactness survives flat scalar extension. -/
theorem ambientPointKoszul_flat_exact_last [Module.Flat R S] (f g h : R)
    (hex : LinearMap.range (threeGeneratorMiddle f g h) =
      LinearMap.ker (threeGeneratorLast f g h)) :
    LinearMap.range (threeGeneratorMiddle (algebraMap R S f) (algebraMap R S g) (algebraMap R S h)) =
      LinearMap.ker (threeGeneratorLast (algebraMap R S f) (algebraMap R S g) (algebraMap R S h)) := by
  have ht : Function.Exact ((threeGeneratorMiddle f g h).lTensor S)
      ((threeGeneratorLast f g h).lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr hex.symm)
  have hexact := Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := ambientPointKoszul_tensorTriple R S) (e₂ := ambientPointKoszul_tensorTriple R S)
    (e₃ := TensorProduct.rid R S)
    (middle_ladder R S f g h) (last_ladder R S f g h) ht
  have h' : Function.Exact
      (threeGeneratorMiddle (algebraMap R S f) (algebraMap R S g) (algebraMap R S h))
      (threeGeneratorLast (algebraMap R S f) (algebraMap R S g) (algebraMap R S h)) := hexact
  exact (LinearMap.exact_iff.mp h').symm

end PfaffianDescent

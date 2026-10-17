import PfaffianDescent.VoisinQuadraticMonomialPartition

/-!
# The quadratic kernel frame on the selected minor open

After localizing at the selected determinant, the eight selected columns
give an isomorphism. The two complementary monomial coefficients therefore
give a regular two-element basis for the block-form evaluation kernel.
-/

namespace PfaffianDescent

open AllCharacteristics.UniversalHomogeneous

universe u

noncomputable def quadraticSelectedOpenBlockBasis
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) :
    let S := Localization.Away (quadraticMinorDet m y)
    let f := algebraMap R S
    let A := (eightPointQuadraticEvaluationMinor m y).map f
    let B := (eightPointQuadraticEvaluationComplement m y).map f
    Module.Basis (Fin 2) S
      (LinearMap.ker (quadraticBlockEvaluation
        (Matrix.toLinearEquiv (Pi.basisFun S (Fin 8)) A
          (quadraticMinor_isUnit_on_principalOpen m y))
        (Matrix.toLin' B))) := by
  dsimp only
  exact quadraticMatrixBlockKernelBasis
    ((eightPointQuadraticEvaluationMinor m y).map
      (algebraMap R (Localization.Away (quadraticMinorDet m y))))
    (quadraticMinor_isUnit_on_principalOpen m y)
    ((eightPointQuadraticEvaluationComplement m y).map
      (algebraMap R (Localization.Away (quadraticMinorDet m y))))

/-- The actual ten-column quadratic evaluation kernel has a regular
two-element basis over the selected determinant principal open. -/
noncomputable def quadraticSelectedOpenFullKernelBasis
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) :
    let S := Localization.Away (quadraticMinorDet m y)
    let f := algebraMap R S
    Module.Basis (Fin 2) S
      (LinearMap.ker (Matrix.toLin'
        (eightPointQuadraticEvaluationMatrix
          (fun k j => f (y k j))))) := by
  dsimp only
  have hA : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => algebraMap R
        (Localization.Away (quadraticMinorDet m y)) (y k j))).det := by
    rw [← eightPointQuadraticEvaluationMinor_map]
    exact quadraticMinor_isUnit_on_principalOpen m y
  exact eightPointQuadraticEvaluationKernelBasis m
    (fun k j => algebraMap R
      (Localization.Away (quadraticMinorDet m y)) (y k j)) hA

theorem quadraticSelectedOpenFullKernelBasis_polynomial_data
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (i : Fin 2) :
    let S := Localization.Away (quadraticMinorDet m y)
    let f := algebraMap R S
    let yS : Fin 8 → Fin 4 → S := fun k j => f (y k j)
    let b := quadraticSelectedOpenFullKernelBasis m y
    (quadraticPolynomialOfCoefficients (b i).1).IsHomogeneous 2 ∧
      ∀ k : Fin 8,
        (quadraticPolynomialOfCoefficients (b i).1).eval (yS k) = 0 := by
  dsimp only
  exact quadraticKernelBasis_polynomial_data
    (fun k j => algebraMap R
      (Localization.Away (quadraticMinorDet m y)) (y k j))
    (quadraticSelectedOpenFullKernelBasis m y) i

theorem quadraticSelectedOpenFullKernelBasis_complement
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (i j : Fin 2) :
    let S := Localization.Away (quadraticMinorDet m y)
    (quadraticSelectedOpenFullKernelBasis m y i).1
      (quadraticMonomialPartition m (Sum.inr j)) =
        (Pi.basisFun S (Fin 2) i) j := by
  dsimp only
  have hA : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => algebraMap R
        (Localization.Away (quadraticMinorDet m y)) (y k j))).det := by
    rw [← eightPointQuadraticEvaluationMinor_map]
    exact quadraticMinor_isUnit_on_principalOpen m y
  simpa [quadraticSelectedOpenFullKernelBasis] using
    (eightPointQuadraticEvaluationKernelBasis_complement m
      (fun k j => algebraMap R
        (Localization.Away (quadraticMinorDet m y)) (y k j)) hA i j)

/-- The actual quadratic equation over the selected determinant open. -/
noncomputable def quadraticSelectedOpenPolynomial
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (i : Fin 2) :
    MvPolynomial (Fin 4) (Localization.Away (quadraticMinorDet m y)) :=
  quadraticPolynomialOfCoefficients
    (quadraticSelectedOpenFullKernelBasis m y i).1

theorem quadraticSelectedOpenPolynomial_isHomogeneous
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (i : Fin 2) :
    (quadraticSelectedOpenPolynomial m y i).IsHomogeneous 2 := by
  exact (quadraticSelectedOpenFullKernelBasis_polynomial_data m y i).1

theorem quadraticSelectedOpenPolynomial_eval_zero
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (i : Fin 2) (k : Fin 8) :
    (quadraticSelectedOpenPolynomial m y i).eval
      (fun j => algebraMap R
        (Localization.Away (quadraticMinorDet m y)) (y k j)) = 0 := by
  exact (quadraticSelectedOpenFullKernelBasis_polynomial_data m y i).2 k

end PfaffianDescent

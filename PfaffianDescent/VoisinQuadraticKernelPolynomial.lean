import PfaffianDescent.VoisinQuadraticGenericKernelRank

/-!
# Turning a quadratic evaluation kernel into equations

The evaluation matrix uses the degree-two monomial coefficient basis. A
coefficient vector in its kernel is therefore an actual homogeneous quadric
vanishing at all eight marked vectors.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.UniversalHomogeneous

universe u

noncomputable def quadraticPolynomialOfCoefficients
    {F : Type u} [CommRing F]
    (v : Monomials (Fin 4) 2 → F) : MvPolynomial (Fin 4) F :=
  ∑ m, C (v m) * monomial m.1 1

theorem quadraticPolynomialOfCoefficients_isHomogeneous
    {F : Type u} [CommRing F]
    (v : Monomials (Fin 4) 2 → F) :
    (quadraticPolynomialOfCoefficients v).IsHomogeneous 2 := by
  classical
  unfold quadraticPolynomialOfCoefficients
  apply IsHomogeneous.sum
  intro m hm
  exact (isHomogeneous_monomial 1 m.2).C_mul (v m)

theorem quadraticPolynomialOfCoefficients_eval
    {F : Type u} [CommRing F]
    (v : Monomials (Fin 4) 2 → F)
    (y : Fin 8 → Fin 4 → F) (k : Fin 8) :
    (quadraticPolynomialOfCoefficients v).eval (y k) =
      (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y) v) k := by
  classical
  simp [quadraticPolynomialOfCoefficients, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, eightPointQuadraticEvaluationMatrix]
  apply Finset.sum_congr rfl
  intro m hm
  exact mul_comm _ _

theorem coeff_quadraticPolynomialOfCoefficients
    {F : Type u} [CommRing F]
    (v : Monomials (Fin 4) 2 → F)
    (m : Monomials (Fin 4) 2) :
    (quadraticPolynomialOfCoefficients v).coeff m.1 = v m := by
  classical
  simp [quadraticPolynomialOfCoefficients, coeff_sum,
    coeff_C_mul, coeff_monomial]
  simp only [Subtype.coe_inj]
  simp

theorem quadraticPolynomialOfCoefficients_injective
    {F : Type u} [CommRing F] :
    Function.Injective
      (quadraticPolynomialOfCoefficients (F := F)) := by
  intro v w h
  funext m
  have hm := congrArg (fun p : MvPolynomial (Fin 4) F => p.coeff m.1) h
  simpa only [coeff_quadraticPolynomialOfCoefficients] using hm

noncomputable def quadraticPolynomialOfCoefficientsLinearMap
    (F : Type u) [CommRing F] :
    (Monomials (Fin 4) 2 → F) →ₗ[F] MvPolynomial (Fin 4) F where
  toFun := quadraticPolynomialOfCoefficients
  map_add' := by
    intro v w
    classical
    simp [quadraticPolynomialOfCoefficients, add_mul,
      Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    classical
    simp [quadraticPolynomialOfCoefficients, Finset.smul_sum,
      MvPolynomial.smul_eq_C_mul, Finset.mul_sum, mul_assoc]

theorem quadraticPolynomialOfCoefficientsLinearMap_injective
    (F : Type u) [CommRing F] :
    Function.Injective (quadraticPolynomialOfCoefficientsLinearMap F) :=
  quadraticPolynomialOfCoefficients_injective

theorem quadraticPolynomialOfCoefficients_eval_zero_of_mem_ker
    {F : Type u} [CommRing F]
    (y : Fin 8 → Fin 4 → F)
    (v : LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y)))
    (k : Fin 8) :
    (quadraticPolynomialOfCoefficients v.1).eval (y k) = 0 := by
  rw [quadraticPolynomialOfCoefficients_eval]
  exact congrFun v.2 k

/-- The two kernel-basis vectors are homogeneous quadrics vanishing at
every marked vector. -/
theorem quadraticKernelBasis_polynomial_data
    {F : Type u} [CommRing F]
    (y : Fin 8 → Fin 4 → F)
    (b : Module.Basis (Fin 2) F
      (LinearMap.ker (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y))))
    (i : Fin 2) :
    (quadraticPolynomialOfCoefficients (b i).1).IsHomogeneous 2 ∧
      ∀ k : Fin 8,
        (quadraticPolynomialOfCoefficients (b i).1).eval (y k) = 0 := by
  exact ⟨quadraticPolynomialOfCoefficients_isHomogeneous _,
    fun k => quadraticPolynomialOfCoefficients_eval_zero_of_mem_ker y (b i) k⟩

end PfaffianDescent

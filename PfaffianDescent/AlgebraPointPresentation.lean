import PfaffianDescent.AlgebraHyperplanes
import PfaffianDescent.AlgebraQuinticPresentation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace PfaffianDescent
open Module

section
variable {K : Type*} [Field K]

/-- Substitution of a linear coordinate change into a matrix pencil. -/
def pencilCompose (P : Fin 4 → Mat K 6) (N : Mat K 4) : Fin 4 → Mat K 6 :=
  fun j => pencil P (fun i => N i j)

theorem pencilCompose_alternating (P : Fin 4 → Mat K 6) (N : Mat K 4)
    (hP : ∀ i, IsAlternating (P i)) : ∀ j, IsAlternating (pencilCompose P N j) :=
  fun j => isAlternating_pencil P hP _

theorem pencilCompose_eval (P : Fin 4 → Mat K 6) (N : Mat K 4) (x : Vec K 4) :
    pencil (pencilCompose P N) x = pencil P (N.mulVec x) := by
  ext r s
  simp only [pencilCompose, pencil, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change x 0 * (N 0 0 * P 0 r s + N 1 0 * P 1 r s + N 2 0 * P 2 r s + N 3 0 * P 3 r s) + x 1 * (N 0 1 * P 0 r s + N 1 1 * P 1 r s + N 2 1 * P 2 r s + N 3 1 * P 3 r s) + x 2 * (N 0 2 * P 0 r s + N 1 2 * P 1 r s + N 2 2 * P 2 r s + N 3 2 * P 3 r s) + x 3 * (N 0 3 * P 0 r s + N 1 3 * P 1 r s + N 2 3 * P 2 r s + N 3 3 * P 3 r s) = (N 0 0 * x 0 + (N 0 1 * x 1 + (N 0 2 * x 2 + (N 0 3 * x 3)))) * P 0 r s + (N 1 0 * x 0 + (N 1 1 * x 1 + (N 1 2 * x 2 + (N 1 3 * x 3)))) * P 1 r s + (N 2 0 * x 0 + (N 2 1 * x 1 + (N 2 2 * x 2 + (N 2 3 * x 3)))) * P 2 r s + (N 3 0 * x 0 + (N 3 1 * x 1 + (N 3 2 * x 2 + (N 3 3 * x 3)))) * P 3 r s
  ring

end

section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Cubics through independent coordinates in a quintic Frobenius hyperplane have
Pfaffian presentations. Both the power basis and the multiplication pairing are explicit. -/
theorem quintic_algebra_tensor_presentation (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) (p : Vec A 4) (hp : LinearIndependent K p)
    (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell)
    (hspan : Submodule.span K (Set.range p) = LinearMap.ker ell)
    (c : Cubic K 4) (hF : (c.map (algebraMap K A)).eval p = 0) :
    ∃ P : Fin 4 → Mat K 6, (∀ i, IsAlternating (P i)) ∧
      ∀ x : Vec K 4, c.eval x = pf6 (pencil P x) := by
  obtain ⟨u, M, hinj, hcoord⟩ := independent_quintic_algebra_coordinates a b hb p hp ell hell hspan
  rw [hcoord, Cubic.eval_smul] at hF
  have hz := (u.isUnit.pow 3).mul_right_eq_zero.mp hF
  have hcomp : ((c.compLinear M).map (algebraMap K A)).eval (rationalCubicCoordinates a) = 0 := by
    rw [Cubic.compLinear_map, Cubic.eval_compLinear]
    exact hz
  obtain ⟨P, hP, hPx⟩ := canonical_algebra_quintic_tensor_presentation a b hb (c.compLinear M) hcomp
  have hdet : IsUnit M.det := M.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  refine ⟨pencilCompose P M⁻¹, pencilCompose_alternating P M⁻¹ hP, ?_⟩
  intro x
  rw [pencilCompose_eval]
  have he := hPx (M⁻¹.mulVec x)
  rw [Cubic.eval_compLinear, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet,
    Matrix.one_mulVec] at he
  exact he

end

section
variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]

/-- The same finite-algebra presentation as an equality of homogeneous polynomials. -/
theorem quintic_algebra_polynomial_presentation (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) (p : Vec A 4) (hp : LinearIndependent K p)
    (ell : Module.Dual K A) (hell : IsFrobeniusFunctional ell)
    (hspan : Submodule.span K (Set.range p) = LinearMap.ker ell)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (hF : MvPolynomial.eval₂ (algebraMap K A) p f = 0) :
    ∃ P : Fin 4 → Mat K 6, (∀ i, IsAlternating (P i)) ∧ (pfaffianCubic P).toMvPolynomial = f := by
  obtain ⟨c, rfl⟩ := homogeneous_cubic_has_tensor f hf
  rw [Cubic.eval_toMvPolynomial] at hF
  obtain ⟨P, hP, he⟩ := quintic_algebra_tensor_presentation a b hb p hp ell hell hspan c hF
  refine ⟨P, hP, ?_⟩
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.eval₂ (RingHom.id K) x (pfaffianCubic P).toMvPolynomial =
    MvPolynomial.eval₂ (RingHom.id K) x c.toMvPolynomial
  rw [Cubic.eval_toMvPolynomial, Cubic.eval_toMvPolynomial]
  change (pfaffianCubic P).eval x = c.eval x
  rw [eval_pfaffianCubic]
  exact (he x).symm

end
end PfaffianDescent

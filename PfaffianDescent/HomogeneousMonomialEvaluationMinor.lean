import PfaffianDescent.VoisinQuadraticEvaluationMatrix
import Mathlib.RingTheory.Localization.Away.Basic

/-!
An invertible monomial evaluation minor for arbitrary numbers of marked
points and arbitrary homogeneous degree. This includes the sixteen-point
cubic minor needed for the first residual intersection.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.UniversalHomogeneous

universe u v

noncomputable def homogeneousPointEvaluationMatrix
    {R : Type u} [CommRing R] (n d : ℕ) (x : Fin n → Fin 4 → R) :
    Matrix (Fin n) (Monomials (Fin 4) d) R :=
  fun i m => (MvPolynomial.monomial m.1 (1 : R)).eval (x i)

noncomputable def homogeneousPointEvaluationMinor
    {R : Type u} [CommRing R] {n d : ℕ}
    (m : Fin n ↪ Monomials (Fin 4) d) (x : Fin n → Fin 4 → R) :
    Matrix (Fin n) (Fin n) R :=
  (homogeneousPointEvaluationMatrix n d x).submatrix id m

theorem homogeneousPointEvaluationMinor_map
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] {n d : ℕ}
    (f : R →+* S) (m : Fin n ↪ Monomials (Fin 4) d)
    (x : Fin n → Fin 4 → R) :
    (homogeneousPointEvaluationMinor m x).map f =
      homogeneousPointEvaluationMinor m (fun i j => f (x i j)) := by
  ext i j
  simp [homogeneousPointEvaluationMinor, homogeneousPointEvaluationMatrix,
    MvPolynomial.eval_monomial]

theorem homogeneousPointEvaluationMatrix_surjective_of_restriction
    {K : Type u} [Field K] (n d : ℕ) (x : Fin n → Fin 4 → K)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := K) (fun j i => x i j) d)) :
    Function.Surjective (Matrix.toLin' (homogeneousPointEvaluationMatrix n d x)) := by
  classical
  intro z
  obtain ⟨q, hq⟩ := hsurj z
  let c : Monomials (Fin 4) d → K := fun m => q.1.coeff m.1
  refine ⟨c, ?_⟩
  funext i
  have hexp := sum_monomial_coeff_eq q.1 q.2
  have heval := congrArg (fun p : MvPolynomial (Fin 4) K => p.eval (x i)) hexp
  calc
    (Matrix.toLin' (homogeneousPointEvaluationMatrix n d x) c) i =
        ∑ m : Monomials (Fin 4) d,
          (MvPolynomial.monomial m.1 (q.1.coeff m.1)).eval (x i) := by
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        homogeneousPointEvaluationMatrix, c, MvPolynomial.eval_monomial, mul_comm]
    _ = q.1.eval (x i) := by simpa only [MvPolynomial.eval_sum] using heval
    _ = z i := by
      simpa [homogeneousSectionRestriction_apply,
        finite_product_evaluation_apply] using congrFun hq i

theorem exists_unit_homogeneousPointEvaluationMinor_of_surjective
    {K : Type u} [Field K] (n d : ℕ) (x : Fin n → Fin 4 → K)
    (hsurj : Function.Surjective
      (Matrix.toLin' (homogeneousPointEvaluationMatrix n d x))) :
    ∃ m : Fin n ↪ Monomials (Fin 4) d,
      IsUnit (homogeneousPointEvaluationMinor m x).det := by
  classical
  let M := homogeneousPointEvaluationMatrix n d x
  have hspan : Submodule.span K (Set.range M.col) = ⊤ := by
    rw [← Matrix.range_toLin']
    exact LinearMap.range_eq_top.mpr hsurj
  obtain ⟨κ, a, ha, hspan', hli⟩ := exists_linearIndependent' K M.col
  letI : Fintype κ := Fintype.ofInjective a ha
  have hselected : Submodule.span K (Set.range (M.col ∘ a)) = ⊤ := by
    rw [hspan', hspan]
  have hcard : Fintype.card κ = n := by
    have hdim := finrank_span_eq_card hli
    rw [hselected, finrank_top, Module.finrank_pi] at hdim
    simpa using hdim.symm
  let e : Fin n ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let m : Fin n ↪ Monomials (Fin 4) d := ⟨a ∘ e, ha.comp e.injective⟩
  have hli_m : LinearIndependent K (fun j : Fin n => M.col (m j)) :=
    hli.comp e e.injective
  have hli_minor : LinearIndependent K (M.submatrix id m).col := by
    convert hli_m using 1
    funext j i
    rfl
  have hunit : IsUnit (M.submatrix id m) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli_minor
  exact ⟨m, (Matrix.isUnit_iff_isUnit_det _).mp hunit⟩

theorem exists_unit_homogeneousPointEvaluationMinor_of_restriction
    {K : Type u} [Field K] (n d : ℕ) (x : Fin n → Fin 4 → K)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := K) (fun j i => x i j) d)) :
    ∃ m : Fin n ↪ Monomials (Fin 4) d,
      IsUnit (homogeneousPointEvaluationMinor m x).det :=
  exists_unit_homogeneousPointEvaluationMinor_of_surjective n d x
    (homogeneousPointEvaluationMatrix_surjective_of_restriction n d x hsurj)

end PfaffianDescent

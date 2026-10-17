import PfaffianDescent.IndependentQuinticPoint
import PfaffianDescent.CubicPointDeformation
import PfaffianDescent.RationalFunctionIndependence
import PfaffianDescent.CubicSpecialization

namespace PfaffianDescent
open Module Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Surjective cubic evaluation permits deformation to a noncoplanar quintic point. -/
theorem cubic_descent_of_quintic_surjective (hdim : finrank K L = 5)
    (c : Cubic K 4) (p : Vec L 4)
    (hF : (c.map (algebraMap K L)).eval p = 0)
    (hsurj : Function.Surjective (cubicEvaluation p : Cubic K 4 →ₗ[K] L)) :
    ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  obtain ⟨α, b, hb⟩ := exists_power_basis_five hdim
  let q : Vec L 4 := fun i => α^(i : ℕ)
  have hq : LinearIndependent K q := by
    have h := b.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective 4)
    simpa only [Function.comp_def, hb, Fin.val_castSucc] using h
  choose d hd using fun j : Fin 5 => hsurj (b j)
  obtain ⟨F, hFP, hF0⟩ := deform_cubic_through_point b p q c hF d hd
  let P := pointDeformation p q
  have hdimR : finrank K⟮X⟯ L⟮X⟯ = 5 := (RatFunc.finrank_ratFunc_ratFunc K L).trans hdim
  let : FiniteDimensional K⟮X⟯ L⟮X⟯ := Module.finite_of_finrank_pos (by rw [hdimR]; decide)
  have hPR : LinearIndependent K⟮X⟯ (fun i => algebraMap L[X] L⟮X⟯ (P i)) := by
    apply rationalFunction_independent_of_specialization P (1 : K)
    simpa only [P, map_one, pointDeformation_one] using hq
  have hcoeff : (F.map (algebraMap K[X] K⟮X⟯)).map (algebraMap K⟮X⟯ L⟮X⟯) =
      (F.map (mapRingHom (algebraMap K L))).map (algebraMap L[X] L⟮X⟯) := by
    funext i
    change algebraMap K⟮X⟯ L⟮X⟯ (algebraMap K[X] K⟮X⟯ (F i)) =
      algebraMap L[X] L⟮X⟯ ((mapRingHom (algebraMap K L)) (F i))
    rw [← IsScalarTower.algebraMap_apply K[X] K⟮X⟯ L⟮X⟯,
      ← Polynomial.algebraMap_def, ← IsScalarTower.algebraMap_apply K[X] L[X] L⟮X⟯]
  have hroot : ((F.map (algebraMap K[X] K⟮X⟯)).map (algebraMap K⟮X⟯ L⟮X⟯)).eval
      (fun i => algebraMap L[X] L⟮X⟯ (P i)) = 0 := by
    rw [hcoeff, Cubic.eval_map, hFP, map_zero]
  obtain ⟨x, hx, he⟩ := cubic_descent_of_independent_quintic_point hdimR
    (F.map (algebraMap K[X] K⟮X⟯)) (fun i => algebraMap L[X] L⟮X⟯ (P i)) hPR hroot
  obtain ⟨y, hy, hFy⟩ := specialize_fraction_cubic_at F 0 x hx he
  rw [hF0] at hFy
  exact ⟨y, hy, hFy⟩

/-- Degree five implies degree one for every homogeneous cubic form in four variables.
This coordinate theorem includes the smooth cubic-surface theorem from the source note,
and does not assume a Pfaffian presentation, general position, or smoothness. -/
theorem cubic_degree_five_descent (hdim : finrank K L = 5)
    (c : Cubic K 4) (p : Vec L 4) (hp : p ≠ 0)
    (hF : (c.map (algebraMap K L)).eval p = 0) :
    ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (funext h)
  let r := (p i)⁻¹ • p
  have hr : r i = 1 := inv_mul_cancel₀ hi
  have hFr : (c.map (algebraMap K L)).eval r = 0 := by
    rw [Cubic.eval_smul, hF, mul_zero]
  rcases quintic_cubic_evaluation_dichotomy hdim c r i hr hFr with h | h
  · exact h
  · exact cubic_descent_of_quintic_surjective hdim c r hFr h

end
end PfaffianDescent

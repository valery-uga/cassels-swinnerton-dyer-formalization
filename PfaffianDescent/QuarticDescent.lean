import PfaffianDescent.QuarticCoordinates
import PfaffianDescent.EvaluationSpan
import PfaffianDescent.CubicPointDeformation
import PfaffianDescent.RationalFunctionIndependence
import PfaffianDescent.CubicSpecialization

namespace PfaffianDescent
open Module Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Surjective cubic evaluation permits deformation to a noncoplanar quartic point. -/
theorem cubic_descent_of_quartic_surjective (hdim : finrank K L = 4)
    (c : Cubic K 4) (p : Vec L 4)
    (hF : (c.map (algebraMap K L)).eval p = 0)
    (hsurj : Function.Surjective (cubicEvaluation p : Cubic K 4 →ₗ[K] L)) :
    ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  obtain ⟨α, b, hb, _⟩ := exists_power_basis_four hdim
  let q : Vec L 4 := fun i => α^(i : ℕ)
  have hq : LinearIndependent K q := by
    rw [show q = b from (funext hb).symm]
    exact b.linearIndependent
  choose d hd using fun j : Fin 4 => hsurj (b j)
  obtain ⟨F, hFP, hF0⟩ := deform_cubic_through_point b p q c hF d hd
  let P := pointDeformation p q
  have hdimR : finrank K⟮X⟯ L⟮X⟯ = 4 := (RatFunc.finrank_ratFunc_ratFunc K L).trans hdim
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
  obtain ⟨x, hx, he⟩ := cubic_descent_of_independent_quartic_point hdimR
    (F.map (algebraMap K[X] K⟮X⟯)) (fun i => algebraMap L[X] L⟮X⟯ (P i)) hPR hroot
  obtain ⟨y, hy, hFy⟩ := specialize_fraction_cubic_at F 0 x hx he
  rw [hF0] at hFy
  exact ⟨y, hy, hFy⟩

/-- Every normalized quartic point either lies over a quadratic subfield or
has surjective cubic evaluation. -/
theorem quartic_cubic_evaluation_dichotomy (hdim : finrank K L = 4)
    (c : Cubic K 4) (p : Vec L 4) (k : Fin 4) (hk : p k = 1)
    (hF : (c.map (algebraMap K L)).eval p = 0) :
    (∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0) ∨
      Function.Surjective (cubicEvaluation p : Cubic K 4 →ₗ[K] L) := by
  let F := IntermediateField.adjoin K (Set.range p)
  by_cases hgen : F = ⊤
  · exact Or.inr (quartic_cubicEvaluation_surjective hdim p k hk hgen)
  left
  have hdvd : finrank K F ∣ 4 := by
    rw [← hdim]
    exact Module.finrank_dvd_finrank_right K F L
  have hle : finrank K F ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hne4 : finrank K F ≠ 4 := by
    intro h
    apply hgen
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [h, IntermediateField.finrank_top', hdim]
  have hne3 : finrank K F ≠ 3 := by
    intro h
    rw [h] at hdvd
    norm_num at hdvd
  have hsmall : finrank K F ≤ 2 := by omega
  let r : Vec F 4 := fun i => ⟨p i, IntermediateField.subset_adjoin K (Set.range p) (Set.mem_range_self i)⟩
  have hr : r ≠ 0 := by
    intro h
    have he := congrArg (fun v : Vec F 4 => (v k : L)) h
    exact one_ne_zero (by simpa only [r, hk, Pi.zero_apply, ZeroMemClass.coe_zero] using he)
  have hcoeff : (c.map (algebraMap K F)).map (algebraMap F L) = c.map (algebraMap K L) := by
    funext i
    exact (IsScalarTower.algebraMap_apply K F L (c i)).symm
  have he : (c.map (algebraMap K F)).eval r = 0 := by
    apply (algebraMap F L).injective
    rw [map_zero, ← Cubic.eval_map, hcoeff]
    exact hF
  exact cubic_degree_le_two_secant hsmall c r hr he

/-- Degree four implies degree one for every homogeneous cubic in four variables. -/
theorem cubic_degree_four_descent (hdim : finrank K L = 4)
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
  rcases quartic_cubic_evaluation_dichotomy hdim c r i hr hFr with h | h
  · exact h
  · exact cubic_descent_of_quartic_surjective hdim c r hFr h

end
end PfaffianDescent

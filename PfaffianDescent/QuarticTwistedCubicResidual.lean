import PfaffianDescent.QuarticBinaryResidual
import PfaffianDescent.QuarticTwistedCubicIdeal
import PfaffianDescent.PolynomialLinearChange

/-!
# The residual point on the twisted cubic

Restricting a cubic hypersurface to the twisted cubic produces a binary
degree-nine form.  A quartic dual point on that curve supplies a rational
residual point.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial

universe u

variable {k : Type u} [Field k]

/-- The cubic Veronese parametrization of the standard twisted cubic. -/
def cubicVeronese {A : Type u} [CommRing A] (s t : A) : Fin 4 → A :=
  ![s ^ 3, s ^ 2 * t, s * t ^ 2, t ^ 3]

theorem cubicVeronese_nonzero (s t : k) (hst : s ≠ 0 ∨ t ≠ 0) :
    cubicVeronese s t ≠ 0 := by
  intro h
  have hs : s ^ 3 = 0 := by simpa [cubicVeronese] using congrFun h 0
  have ht : t ^ 3 = 0 := by simpa [cubicVeronese] using congrFun h 3
  exact hst.elim
    (fun hn => hn ((pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hs))
    (fun hn => hn ((pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp ht))

theorem standardTwistedCubicParam_homogeneous {F : MvPolynomial (Fin 4) k} {n : ℕ}
    (hF : F.IsHomogeneous n) : (standardTwistedCubicParam k F).IsHomogeneous (3 * n) := by
  apply hF.aeval
  intro i
  fin_cases i
  · exact isHomogeneous_X_pow 0 3
  · exact (isHomogeneous_X_pow 0 2).mul (isHomogeneous_X k 1)
  · exact (isHomogeneous_X k 0).mul (isHomogeneous_X_pow 1 2)
  · exact isHomogeneous_X_pow 1 3

theorem standardTwistedCubicParam_eval {A : Type u} [CommRing A] [Algebra k A]
    (s t : A) (F : MvPolynomial (Fin 4) k) :
    aeval ![s, t] (standardTwistedCubicParam k F) = aeval (cubicVeronese s t) F := by
  have h : (aeval ![s, t]).comp (standardTwistedCubicParam k) =
      aeval (cubicVeronese s t) := by
    ext i : 1
    fin_cases i <;> simp [standardTwistedCubicParam, cubicVeronese]
  exact AlgHom.congr_fun h F

/-- A cubic hypersurface containing a separable quartic double point on the
standard twisted cubic has a rational point. -/
theorem cubic_point_of_twisted_cubic_double_point
    {L : Type u} [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    (a b : L) (hb : b ≠ 0) (ha : (minpoly k a).natDegree = 4)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hjet : aeval (cubicVeronese (1 : DualNumber L)
      (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b)) F = 0) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ aeval x F = 0 := by
  obtain ⟨z, hz, hval⟩ := binary_degree_nine_residual_point a b hb ha
    (standardTwistedCubicParam k F) (standardTwistedCubicParam_homogeneous hF)
    (by rwa [standardTwistedCubicParam_eval])
  have hst : z 0 ≠ 0 ∨ z 1 ≠ 0 := by
    by_contra! h
    apply hz
    funext i
    fin_cases i <;> simp [h.1, h.2]
  have hvec : ![z 0, z 1] = z := by
    funext i
    fin_cases i <;> rfl
  refine ⟨cubicVeronese (z 0) (z 1), cubicVeronese_nonzero _ _ hst, ?_⟩
  rw [← standardTwistedCubicParam_eval, hvec]
  exact hval

/-- An invertible linear coordinate change transports the residual-point
argument from the standard twisted cubic to any of its linear images. -/
theorem cubic_point_of_coordinate_changed_twisted_cubic_double_point
    (M : Matrix (Fin 4) (Fin 4) k) (hM : IsUnit M.det)
    {L : Type u} [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    (a b : L) (hb : b ≠ 0) (ha : (minpoly k a).natDegree = 4)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hjet : aeval (cubicVeronese (1 : DualNumber L)
      (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b)) (linearSubstitution M F) = 0) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ aeval x F = 0 := by
  obtain ⟨z, hz, hval⟩ := cubic_point_of_twisted_cubic_double_point a b hb ha
    (linearSubstitution M F) (linearSubstitution_homogeneous M hF) hjet
  refine ⟨M.mulVec z, ?_, ?_⟩
  · intro hzero
    apply hz
    apply (Matrix.mulVec_injective_iff_isUnit.mpr (M.isUnit_iff_isUnit_det.mpr hM))
    simpa using hzero
  · rw [← linearSubstitution_eval]
    exact hval

end QuarticNet
end PfaffianDescent

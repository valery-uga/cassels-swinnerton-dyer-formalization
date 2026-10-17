import PfaffianDescent.QuarticFiniteNet

/-!
# The four-cycle branch of the Section 4 tangent net
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module TrivSqZeroExt

section
variable {K : Type*} [Field K]

/-- Denominator-free coefficients for the three quadrics in the four-cycle
branch.  The third is `bcde` times the paper's third quadric. -/
def fourCycleScaledQuadrics (b c d e : K) : Fin 3 → Fin 6 → K :=
  ![![1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1],
    ![0, c * d * e, -b * d * e, -b * c * e, b * c * d, 0]]

noncomputable def fourCycleScaledQuadricPolynomials (b c d e : K) :
    Fin 3 → MvPolynomial (Fin 4) K :=
  fun i => offDiagonalQuadric (fourCycleScaledQuadrics b c d e i)

theorem fourCycleScaledQuadricPolynomials_homogeneous (b c d e : K) (i : Fin 3) :
    (fourCycleScaledQuadricPolynomials b c d e i).IsHomogeneous 2 :=
  offDiagonalQuadric_homogeneous _

theorem tangentQuadricEvaluation_fourCycleScaledQuadrics
    (b c d e : K) :
    tangentQuadricEvaluation (skewTangentDirections 0 b c d e 0)
      (fourCycleScaledQuadrics b c d e 0) = 0 ∧
    tangentQuadricEvaluation (skewTangentDirections 0 b c d e 0)
      (fourCycleScaledQuadrics b c d e 1) = 0 ∧
    tangentQuadricEvaluation (skewTangentDirections 0 b c d e 0)
      (fourCycleScaledQuadrics b c d e 2) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;>
    simp [tangentQuadricEvaluation, skewTangentDirections, fourCycleScaledQuadrics] <;> ring

theorem fourCycleScaledQuadricPolynomials_vanish
    (b c d e : K) (i : Fin 3) (j : Fin 4) :
    aeval (tangentDualPoint (skewTangentDirections 0 b c d e 0) j)
      (fourCycleScaledQuadricPolynomials b c d e i) = 0 := by
  have hdiag : ∀ r, skewTangentDirections 0 b c d e 0 r r = 0 := by
    intro r
    fin_cases r <;> rfl
  rw [fourCycleScaledQuadricPolynomials,
    offDiagonalQuadric_tangentDualPoint_eval _ hdiag]
  obtain ⟨h0, h1, h2⟩ := tangentQuadricEvaluation_fourCycleScaledQuadrics b c d e
  fin_cases i
  · apply TrivSqZeroExt.ext
    · simp
    · simpa [fourCycleScaledQuadrics] using congrFun h0 j
  · apply TrivSqZeroExt.ext
    · simp
    · simpa [fourCycleScaledQuadrics] using congrFun h1 j
  · apply TrivSqZeroExt.ext
    · simp
    · simpa [fourCycleScaledQuadrics] using congrFun h2 j

/-- The four-cycle ideal-membership conclusion once the product independence
has been established. -/
theorem cubic_mem_fourCycleScaled_ideal_of_tangent_vanishing
    (b c d e : K) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hind : LinearIndependent K (linearQuadricProducts (fourCycleScaledQuadricPolynomials b c d e)))
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections 0 b c d e 0) i) F = 0) :
    F ∈ Ideal.span (Set.range (fourCycleScaledQuadricPolynomials b c d e)) := by
  have hdiag (i : Fin 4) : skewTangentDirections 0 b c d e 0 i i = 0 := by
    fin_cases i <;> rfl
  have hn (i : Fin 4) : ∃ j, skewTangentDirections 0 b c d e 0 i j ≠ 0 := by
    fin_cases i
    · exact ⟨2, hb⟩
    · exact ⟨2, hd⟩
    · exact ⟨0, neg_ne_zero.mpr hb⟩
    · exact ⟨0, neg_ne_zero.mpr hc⟩
  exact cubic_ideal_membership_of_linear_products _ hdiag hn
    (fourCycleScaledQuadricPolynomials b c d e)
    (fourCycleScaledQuadricPolynomials_homogeneous b c d e)
    (fourCycleScaledQuadricPolynomials_vanish b c d e) hind F hF hvan

end
end QuarticNet
end PfaffianDescent

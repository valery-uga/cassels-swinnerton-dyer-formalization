import PfaffianDescent.QuarticTangentInterpolation

/-!
# The finite branch of the Section 4 tangent net

The three quadrics are scaled to remove denominators.  Their twelve linear
multiples are independent precisely in the nonexceptional `Δ ≠ 0` branch.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module TrivSqZeroExt

section
variable {K : Type*} [Field K]

/-- The polynomial associated to a six-tuple of off-diagonal quadric
coefficients in the order `01, 02, 03, 12, 13, 23`. -/
noncomputable def offDiagonalQuadric (q : Fin 6 → K) : MvPolynomial (Fin 4) K :=
  C (q 0) * X 0 * X 1 + C (q 1) * X 0 * X 2 + C (q 2) * X 0 * X 3 +
    C (q 3) * X 1 * X 2 + C (q 4) * X 1 * X 3 + C (q 5) * X 2 * X 3

theorem offDiagonalQuadric_homogeneous (q : Fin 6 → K) :
    (offDiagonalQuadric q).IsHomogeneous 2 := by
  dsimp [offDiagonalQuadric]
  repeat' apply IsHomogeneous.add
  all_goals exact ((isHomogeneous_X K _).C_mul _).mul (isHomogeneous_X K _)

/-- Evaluation of an off-diagonal quadric at a tangent dual point records the
corresponding directional evaluation in its infinitesimal component. -/
theorem offDiagonalQuadric_tangentDualPoint_eval
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0)
    (q : Fin 6 → K) (i : Fin 4) :
    aeval (tangentDualPoint U i) (offDiagonalQuadric q) =
      TrivSqZeroExt.inr (tangentQuadricEvaluation U q i) := by
  fin_cases i <;>
    apply TrivSqZeroExt.ext <;>
    simp [offDiagonalQuadric, tangentDualPoint, tangentQuadricEvaluation,
      hdiag, TrivSqZeroExt.algebraMap_eq_inl] <;> ring

/-- The denominator-free versions of the three explicit quadrics in the
nondegenerate base-locus calculation. -/
def scaledBaseLocusQuadrics (a b c d e f : K) : Fin 3 → Fin 6 → K :=
  ![![b * d, -a * d, 0, a * b, 0, 0],
    ![c * e, 0, -a * e, 0, a * c, 0],
    ![0, c * f, -b * f, 0, 0, b * c]]

/-- The three scaled quadrics as actual homogeneous polynomials. -/
noncomputable def scaledBaseLocusQuadricPolynomials (a b c d e f : K) :
    Fin 3 → MvPolynomial (Fin 4) K :=
  fun i => offDiagonalQuadric (scaledBaseLocusQuadrics a b c d e f i)

theorem scaledBaseLocusQuadricPolynomials_homogeneous (a b c d e f : K) (i : Fin 3) :
    (scaledBaseLocusQuadricPolynomials a b c d e f i).IsHomogeneous 2 :=
  offDiagonalQuadric_homogeneous _

theorem tangentQuadricEvaluation_scaledBaseLocusQuadrics
    (a b c d e f : K) :
    tangentQuadricEvaluation (skewTangentDirections a b c d e f)
      (scaledBaseLocusQuadrics a b c d e f 0) = 0 ∧
    tangentQuadricEvaluation (skewTangentDirections a b c d e f)
      (scaledBaseLocusQuadrics a b c d e f 1) = 0 ∧
    tangentQuadricEvaluation (skewTangentDirections a b c d e f)
      (scaledBaseLocusQuadrics a b c d e f 2) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;>
    simp [tangentQuadricEvaluation, skewTangentDirections, scaledBaseLocusQuadrics] <;> ring

theorem scaledBaseLocusQuadricPolynomials_vanish
    (a b c d e f : K) (i : Fin 3) (j : Fin 4) :
    aeval (tangentDualPoint (skewTangentDirections a b c d e f) j)
      (scaledBaseLocusQuadricPolynomials a b c d e f i) = 0 := by
  have hdiag : ∀ r, skewTangentDirections a b c d e f r r = 0 := by
    intro r
    fin_cases r <;> rfl
  rw [scaledBaseLocusQuadricPolynomials,
    offDiagonalQuadric_tangentDualPoint_eval _ hdiag]
  obtain ⟨h0, h1, h2⟩ := tangentQuadricEvaluation_scaledBaseLocusQuadrics a b c d e f
  fin_cases i
  · apply TrivSqZeroExt.ext
    · simp
    · simpa [scaledBaseLocusQuadrics] using congrFun h0 j
  · apply TrivSqZeroExt.ext
    · simp
    · simpa [scaledBaseLocusQuadrics] using congrFun h1 j
  · apply TrivSqZeroExt.ext
    · simp
    · simpa [scaledBaseLocusQuadrics] using congrFun h2 j

/-- The six coefficient relations left after the six immediately unique cubic
monomials have been removed. -/
theorem scaled_net_remaining_coefficients_zero
    (a b c d e f u v w x y z : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (hdelta : baseLocusDelta a b c d e f ≠ 0)
    (hE : b * d * u + c * e * v = 0)
    (hF : -a * d * u + c * f * w = 0)
    (hA : a * b * u + c * e * y + c * f * z = 0)
    (hB : b * d * x + a * c * v - b * f * z = 0)
    (hC : -a * d * x - a * e * y + b * c * w = 0)
    (hD : a * b * x + a * c * y + b * c * z = 0) :
    u = 0 ∧ v = 0 ∧ w = 0 ∧ x = 0 ∧ y = 0 ∧ z = 0 := by
  have hu : a * b * baseLocusDelta a b c d e f * u = 0 := by
    dsimp [baseLocusDelta]
    linear_combination a * b * e * f * hA + a * c * e * f * hB +
      b * c * e * f * hC - a ^ 2 * c * f * hE - b ^ 2 * c * e * hF
  have hz : baseLocusDelta a b c d e f * z = 0 := by
    dsimp [baseLocusDelta]
    linear_combination d * e * hD - a * e * hB - a * d * hA + a ^ 2 * hE
  have hu0 := (mul_eq_zero.mp hu).resolve_left
    (mul_ne_zero (mul_ne_zero ha hb) hdelta)
  have hz0 := (mul_eq_zero.mp hz).resolve_left hdelta
  have hv0 : v = 0 := by simpa [hu0, hc, he] using hE
  have hw0 : w = 0 := by simpa [hu0, hc, hf] using hF
  have hx0 : x = 0 := by simpa [hv0, hz0, hb, hd] using hB
  have hy0 : y = 0 := by simpa [hu0, hz0, hc, he] using hA
  exact ⟨hu0, hv0, hw0, hx0, hy0, hz0⟩


/-- The finite-branch ideal-membership conclusion, with the twelve-product
independence supplied by the coefficient calculation for the chosen net. -/
theorem cubic_mem_scaledBaseLocus_ideal_of_tangent_vanishing
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hind : LinearIndependent K
      (linearQuadricProducts (scaledBaseLocusQuadricPolynomials a b c d e f)))
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections a b c d e f) i) F = 0) :
    F ∈ Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) := by
  have hdiag (i : Fin 4) : skewTangentDirections a b c d e f i i = 0 := by
    fin_cases i <;> rfl
  have hn (i : Fin 4) : ∃ j, skewTangentDirections a b c d e f i j ≠ 0 := by
    fin_cases i
    · exact ⟨1, ha⟩
    · exact ⟨0, neg_ne_zero.mpr ha⟩
    · exact ⟨0, neg_ne_zero.mpr hb⟩
    · exact ⟨0, neg_ne_zero.mpr hc⟩
  exact cubic_ideal_membership_of_linear_products _ hdiag hn
    (scaledBaseLocusQuadricPolynomials a b c d e f)
    (scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f)
    (scaledBaseLocusQuadricPolynomials_vanish a b c d e f) hind F hF hvan

end
end QuarticNet
end PfaffianDescent

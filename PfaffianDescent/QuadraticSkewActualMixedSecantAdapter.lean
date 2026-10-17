import PfaffianDescent.QuadraticSkewOriginalPairedCubicBridge
import PfaffianDescent.QuadraticSkewLineSecantCoordinates
/-! SOURCE ONLY / UNVERIFIED. Exact twelve-coefficient adapter to the
checked secant algebra, derived from the original equation rather than
assuming a cubic normal-form certificate. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.ActualSecant
open MvPolynomial Module
open QuarticNet MixedNormalForm OriginalBridge
open scoped BigOperators
universe u v
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

def mixedCoefficients (G : MvPolynomial (Fin 4) E) : SplitMixedCubicCoefficients E where
  left := ![G.coeff (leftMixedExponent 0 0), G.coeff (leftMixedExponent 0 1),
    G.coeff (leftMixedExponent 1 0), G.coeff (leftMixedExponent 1 1),
    G.coeff (leftMixedExponent 2 0), G.coeff (leftMixedExponent 2 1)]
  right := ![G.coeff (rightMixedExponent 0 0), G.coeff (rightMixedExponent 0 1),
    G.coeff (rightMixedExponent 1 0), G.coeff (rightMixedExponent 1 1),
    G.coeff (rightMixedExponent 2 0), G.coeff (rightMixedExponent 2 1)]

def mappedMixedCoefficients {R : Type v} [CommRing R]
    (f : E →+* R) (G : MvPolynomial (Fin 4) E) : SplitMixedCubicCoefficients R where
  left := fun i => f ((mixedCoefficients G).left i)
  right := fun i => f ((mixedCoefficients G).right i)

theorem leftMixedPolynomial_eq_secant_left (G : MvPolynomial (Fin 4) E) :
    leftMixedPolynomial G =
      leftMixedValue (mappedMixedCoefficients C G) (X 0) (X 1) (X 2) (X 3) := by
  simp only [leftMixedPolynomial, Fintype.sum_prod_type,
    Fin.sum_univ_three, Fin.sum_univ_two, leftMixedExponent_monomial]
  simp [leftMixedValue, mappedMixedCoefficients, mixedCoefficients] <;> ring

theorem rightMixedPolynomial_eq_secant_right (G : MvPolynomial (Fin 4) E) :
    rightMixedPolynomial G =
      rightMixedValue (mappedMixedCoefficients C G) (X 0) (X 1) (X 2) (X 3) := by
  simp only [rightMixedPolynomial, Fintype.sum_prod_type,
    Fin.sum_univ_three, Fin.sum_univ_two, rightMixedExponent_monomial]
  simp [rightMixedValue, mappedMixedCoefficients, mixedCoefficients] <;> ring

theorem cubic_eq_splitCubicValue
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3)
    (hLeft : G ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : G ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E))) :
    G = splitCubicValue (mappedMixedCoefficients C G) (X 0) (X 1) (X 2) (X 3) := by
  calc
    G = leftMixedPolynomial G + rightMixedPolynomial G :=
      cubic_eq_twelve_mixed_monomials G hG hLeft hRight
    _ = splitCubicValue (mappedMixedCoefficients C G) (X 0) (X 1) (X 2) (X 3) := by
      rw [leftMixedPolynomial_eq_secant_left, rightMixedPolynomial_eq_secant_right]
      rfl

/-- Ring-valued evaluation of the actual cubic equals the checked secant
normal form over every coefficient algebra, including polynomial rings. -/
theorem eval₂_eq_splitCubicValue
    {R : Type v} [CommRing R] (f : E →+* R) (x : Fin 4 → R)
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3)
    (hLeft : G ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : G ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E))) :
    MvPolynomial.eval₂ f x G =
      splitCubicValue (mappedMixedCoefficients f G) (x 0) (x 1) (x 2) (x 3) := by
  conv_lhs => rw [cubic_eq_splitCubicValue G hG hLeft hRight]
  simp [splitCubicValue, leftMixedValue, rightMixedValue,
    mappedMixedCoefficients, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]

/-- The checked secant coefficient arrays are conjugate entry by entry. -/
theorem mixedCoefficients_exchange
    (σ : E ≃ₐ[k] E) (G : MvPolynomial (Fin 4) E)
    (hExchange : MvPolynomial.map σ.toRingHom G = MvPolynomial.rename pairSwap G) :
    ∀ i : Fin 6, σ ((mixedCoefficients G).left i) = (mixedCoefficients G).right i := by
  intro i
  fin_cases i
  · simpa [mixedCoefficients] using conjugate_mixed_coefficients_exchange σ G hExchange 0 0
  · simpa [mixedCoefficients] using conjugate_mixed_coefficients_exchange σ G hExchange 0 1
  · simpa [mixedCoefficients] using conjugate_mixed_coefficients_exchange σ G hExchange 1 0
  · simpa [mixedCoefficients] using conjugate_mixed_coefficients_exchange σ G hExchange 1 1
  · simpa [mixedCoefficients] using conjugate_mixed_coefficients_exchange σ G hExchange 2 0
  · simpa [mixedCoefficients] using conjugate_mixed_coefficients_exchange σ G hExchange 2 1

/-- Actual cubic evaluation at the residual vector vanishes without any
additional normal-form premise. The frame is the one derived in packet 003. -/
theorem actual_mixed_cubic_residual_on_equation
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3)
    (hLeft : G ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 4) E)))
    (hRight : G ∈ Ideal.span ({X 2, X 3} : Set (MvPolynomial (Fin 4) E)))
    (t z : E) :
    MvPolynomial.eval (residualCoordinates (mixedCoefficients G) t z) G = 0 := by
  change MvPolynomial.eval₂ (RingHom.id E)
    (residualCoordinates (mixedCoefficients G) t z) G = 0
  rw [eval₂_eq_splitCubicValue (RingHom.id E) _ G hG hLeft hRight]
  have hc : mappedMixedCoefficients (RingHom.id E) G = mixedCoefficients G := by
    rfl
  rw [hc]
  exact residualCoordinates_on_cubic (mixedCoefficients G) t z

end PfaffianDescent.QuadraticSkewRationality.ActualSecant

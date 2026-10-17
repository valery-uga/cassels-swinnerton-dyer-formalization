import PfaffianDescent.QuadraticSkewOriginalPairedFieldReconstruction
/-! SOURCE ONLY / UNVERIFIED. Exact descended original inverse fractions
give the conjugate parameters used by original-coordinate reconstruction. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open MvPolynomial Module OriginalBridge
universe u v
variable {k E : Type u} {L : Type v}
variable [Field k] [Field E] [Field L] [Algebra k E]

theorem descended_denominator_field_value
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →+* L)
    (Q : MvPolynomial (Fin 4) k)
    (hQ : MvPolynomial.map (algebraMap k E) Q =
      pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2)
    (w : Fin 4 → L) :
    Q.eval₂ (f.comp (algebraMap k E)) w =
      pairedValues C f w 0 * pairedValues C f w 2 := by
  rw [← MvPolynomial.eval₂_map, hQ, MvPolynomial.eval₂_mul]
  rfl

theorem descended_denominator_field_value_ne_zero
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →+* L)
    (Q : MvPolynomial (Fin 4) k)
    (hQ : MvPolynomial.map (algebraMap k E) Q =
      pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2)
    (w : Fin 4 → L) (hQw : Q.eval₂ (f.comp (algebraMap k E)) w ≠ 0) :
    pairedValues C f w 0 ≠ 0 ∧ pairedValues C f w 2 ≠ 0 := by
  rw [descended_denominator_field_value C f Q hQ w] at hQw
  exact mul_ne_zero_iff.mp hQw

theorem descended_inverse_numerators_field_values
    (C : Basis (Fin 4) E (Fin 4 → E)) (f : E →+* L)
    (α β : E) (Q R_T R_U : MvPolynomial (Fin 4) k)
    (hQ : MvPolynomial.map (algebraMap k E) Q =
      pairedInverseCoordinates C 0 * pairedInverseCoordinates C 2)
    (hT : MvPolynomial.map (algebraMap k E) R_T = MvPolynomial.C (α - β)⁻¹ *
      (MvPolynomial.C α * pairedInverseCoordinates C 3 * pairedInverseCoordinates C 0 -
        MvPolynomial.C β * pairedInverseCoordinates C 1 * pairedInverseCoordinates C 2))
    (hU : MvPolynomial.map (algebraMap k E) R_U = MvPolynomial.C (α - β)⁻¹ *
      (pairedInverseCoordinates C 1 * pairedInverseCoordinates C 2 -
        pairedInverseCoordinates C 3 * pairedInverseCoordinates C 0))
    (w : Fin 4 → L) :
    R_T.eval₂ (f.comp (algebraMap k E)) w /
        Q.eval₂ (f.comp (algebraMap k E)) w = inverseT (f α) (f β) (pairedValues C f w) ∧
    R_U.eval₂ (f.comp (algebraMap k E)) w /
        Q.eval₂ (f.comp (algebraMap k E)) w = inverseU (f α) (f β) (pairedValues C f w) := by
  rw [descended_denominator_field_value C f Q hQ w]
  constructor
  · rw [← MvPolynomial.eval₂_map, hT]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C,
      map_inv₀, map_sub]
    rfl
  · rw [← MvPolynomial.eval₂_map, hU]
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C,
      map_inv₀, map_sub]
    rfl

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005

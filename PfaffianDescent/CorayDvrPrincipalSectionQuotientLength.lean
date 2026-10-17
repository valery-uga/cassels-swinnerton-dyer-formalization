import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! Native composition length of the original principal section quotient
over a DVR. The actual ideal, quotient ring and native R-module action
are retained. No supplied length, valuation or finite-length certificate.
This is local algebra, not yet a scheme-stalk cokernel comparison.
SOURCE ONLY / UNVERIFIED: root alone compiles. -/
noncomputable section
namespace PfaffianDescent.Coray
open IsLocalRing IsDiscreteValuationRing
universe u

/-- For an actual nonzero coefficient a in a DVR, the length of the
literal quotient R/(a) is its actual additive valuation. A uniformizer
and unit-times-power expression are constructed internally. Units give
the included length-zero case. -/
theorem dvr_principalSectionQuotient_length
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({a} : Set R)) = addVal R a := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible ha hϖ
  have hI : Ideal.span ({a} : Set R) = maximalIdeal R ^ n := by
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit,
      hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  calc
    Module.length R (R ⧸ Ideal.span ({a} : Set R)) = (n : ENat) := by
      rw [hI]
      exact length_quotient_pow_maximalIdeal R n
    _ = addVal R a := (addVal_def a u hϖ n hu).symm

/-- Finite composition length follows for the SAME original quotient
of a DVR by the SAME nonzero coefficient. No finite-module or Artinian
conclusion is assumed. -/
theorem dvr_principalSectionQuotient_isFiniteLength
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (ha : a ≠ 0) :
    IsFiniteLength R (R ⧸ Ideal.span ({a} : Set R)) := by
  apply Module.length_ne_top_iff.mp
  rw [dvr_principalSectionQuotient_length R a ha]
  exact fun h => ha (addVal_eq_top_iff.mp h)

end PfaffianDescent.Coray

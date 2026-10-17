import PfaffianDescent.FrameArtinInjective
import PfaffianDescent.FrameArtinianReduction

namespace PfaffianDescent
section
variable {K : Type*} [Field K] [CharZero K]

/-- The actual quotient by the five quadrics and the regular linear form is
injective over itself, so it is an Artinian Gorenstein ring. -/
theorem frameQuotient_self_injective : Module.Injective (FrameQuotient K) (FrameQuotient K) :=
  injective_of_frobenius_equiv FrameQuotient.algebraEquiv
    FrameArtin.topCoefficient FrameArtin.topCoefficient_frobenius

/-- The quotient of the homogeneous coordinate ring by the displayed linear form
has injective dimension zero over itself. -/
theorem frameArtinianReduction_self_injective :
    Module.Injective (FrameCoordinateRing K ⧸ Ideal.span {FrameCoordinateRing.ell})
      (FrameCoordinateRing K ⧸ Ideal.span {FrameCoordinateRing.ell}) := by
  let e : (FrameCoordinateRing K ⧸ Ideal.span {FrameCoordinateRing.ell}) ≃ₐ[K] FrameArtin K :=
    (frameArtinianReductionEquiv (K := K)).trans FrameQuotient.algebraEquiv
  exact injective_of_frobenius_equiv (K := K) (A := FrameArtin K)
    (B := FrameCoordinateRing K ⧸ Ideal.span {FrameCoordinateRing.ell}) e
    (FrameArtin.topCoefficient (K := K)) (FrameArtin.topCoefficient_frobenius (K := K))

end
end PfaffianDescent

import PfaffianDescent.NativePolynomialChartArtinianCriterion316
import PfaffianDescent.NativeSpecLocalSmoothLocus316
import PfaffianDescent.MonomialPolynomialLocusSmoothOpen312

/-! Concrete chart Artinian lifts imply membership in the ACTUAL global
polynomial Hilbert smooth open. The geometric lifting premise remains explicit. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

theorem monomialPolynomialContainment_memSmooth_of_chart_tests316
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (m n : ℕ) (p : MvPolynomial (Fin m) R)
    (i : MonomialCoefficientChartIndex300 m n)
    (q : PrimeSpectrum (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))
    {k : ℕ}
    (f : MvPolynomial (Fin k) R →ₐ[R]
      MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)
    (hf : Function.Surjective f)
    (hlift : LocalPolynomialArtinianChartLifts316 f hf q.asIdeal) :
    monomialClosedCoefficientChartToLocus312 R m n p i q ∈
      monomialPolynomialContainmentSmoothOpen312 R m n p := by
  letI := monomialPolynomialContainmentCoefficientAlgebra_finitePresentation312 R m n p i
  have hs := formallySmooth_atPrime_of_polynomial_chart_lifts316 f hf q.asIdeal hlift
  have hm := nativeSpec_mem_smoothLocus_of_localization316 R
    (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) q hs
  change q ∈ (monomialClosedCoefficientChartToLocus312 R m n p i ⁻¹ᵁ
    monomialPolynomialContainmentSmoothOpen312 R m n p)
  rw [monomialPolynomialContainmentSmoothOpen_chart312]
  exact hm

end PfaffianDescent
end

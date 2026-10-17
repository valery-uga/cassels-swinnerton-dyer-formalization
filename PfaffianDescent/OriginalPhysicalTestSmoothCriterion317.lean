import PfaffianDescent.OriginalPhysicalFamilyCoefficientLift317
import PfaffianDescent.MonomialPolynomialChartArtinianSmooth316

/-! Physical canonical test lifts imply smoothness of the original coefficient
chart. This internal criterion keeps its physical-lift premise explicit; the
original closed-point construction supplies that premise separately. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IsLocalRing
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (n : ℕ)
  (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d)
  (j : Fin 4) (hn : 0 < n) (i : MonomialCoefficientChartIndex300 3 n)
variable {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R]
  MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
    (originalNormalizedHypersurfacePolynomial312 r j) i) (hf : Function.Surjective f)
  (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
    (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
local notation "P" => Localization.AtPrime (q.comap f.toRingHom)
local notation "I" => RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
local notation "m" => maximalIdeal P
local notation "TestB" => fun N : ℕ => P ⧸ obstructionThickIdeal316 m I N
local notation "TestS" => fun N : ℕ => P ⧸ obstructionThinIdeal316 m I N

/-- Exact PHYSICAL normalized lifts of the canonical thick-to-thin tests. -/
def OriginalPolynomialPhysicalTestLifts317 : Prop :=
  ∀ N : ℕ, 0 < N →
    ∃ Q : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := TestB N)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R (TestB N))) j)
        (algebraMap (TestB N)
          (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R (TestB N))) j)))) n,
      originalNormalizedAffinePointReduction317 R
          (Ideal.Quotient.factorₐ R (obstructionThickIdeal_le_thin316 m I N)) r hr j n Q =
        originalCoefficientTestPhysicalFamily317 R n r hr j hn i
          (localPolynomialArtinianChartTest316 f hf q N)

/-- The square-zero kernel is derived from the actual local presentation.
The accepted physical-family classifier bridge produces the SAME chart lift. -/
lemma originalPolynomialChartLifts_of_physicalTests317
    (hlift : OriginalPolynomialPhysicalTestLifts317 R n r hr j hn i f hf q) :
    LocalPolynomialArtinianChartLifts316 f hf q := by
  intro N hN
  obtain ⟨Q, hQ⟩ := hlift N hN
  have hnil : IsNilpotent (RingHom.ker
      (Ideal.Quotient.factorₐ R (obstructionThickIdeal_le_thin316 m I N)).toRingHom) :=
    ⟨2, obstructionQuotientReduction_kernel_sq_zero316 m I N
      (localPolynomialPresentation_kernel_le_maximal316 f q)⟩
  obtain ⟨l, hl, _⟩ := originalCoefficientChart_lift_of_physicalNormalizedFamily317
    R n r hr j hn i
    (Ideal.Quotient.factorₐ R (obstructionThickIdeal_le_thin316 m I N))
    (localPolynomialArtinianChartTest316 f hf q N) Q hQ
    (Ideal.Quotient.factor_surjective (obstructionThickIdeal_le_thin316 m I N)) hnil
  exact ⟨l, hl⟩

lemma originalCoefficient_formallySmooth_of_physicalTests317 [IsNoetherianRing R]
    (hlift : OriginalPolynomialPhysicalTestLifts317 R n r hr j hn i f hf q) :
    Algebra.FormallySmooth R (Localization.AtPrime q) :=
  formallySmooth_atPrime_of_polynomial_chart_lifts316 f hf q
    (originalPolynomialChartLifts_of_physicalTests317 R n r hr j hn i f hf q hlift)

/-- The same physical tests place the chart point in the actual global
polynomial Hilbert smooth open. This is an internal criterion, not a claim
that the physical-test hypothesis has already been constructed. -/
lemma originalCoefficient_memSmooth_of_physicalTests317 [IsNoetherianRing R]
    (q₀ : PrimeSpectrum (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i))
    (hlift : OriginalPolynomialPhysicalTestLifts317 R n r hr j hn i f hf q₀.asIdeal) :
    monomialClosedCoefficientChartToLocus312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i q₀ ∈
      monomialPolynomialContainmentSmoothOpen312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) :=
  monomialPolynomialContainment_memSmooth_of_chart_tests316 R 3 n
    (originalNormalizedHypersurfacePolynomial312 r j) i q₀ f hf
    (originalPolynomialChartLifts_of_physicalTests317 R n r hr j hn i f hf q₀.asIdeal hlift)

end PfaffianDescent
end

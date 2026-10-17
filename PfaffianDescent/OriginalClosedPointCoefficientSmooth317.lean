import PfaffianDescent.OriginalCanonicalTestPhysicalLift317
import PfaffianDescent.OriginalPhysicalTestSmoothCriterion317

/-! SOURCE ONLY317. The ORIGINAL smooth cubic and closed point produce an
actual original coefficient-chart point in the actual polynomial Hilbert
smooth open. Physical test lifts and polynomial presentation are constructed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- INTERNAL consumption cut. All physical presentations are already proved
by the original closed-point producer; choose finite polynomial f internally
using the accepted312 finite presentation of the SAME coefficient quotient. -/
private theorem originalKernelPoint_memSmooth_of_allPhysicalPresentations317
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d)
    (j : Fin 4) (hn : 0 < n) (i : MonomialCoefficientChartIndex300 3 n)
    (K : Type u) [Field K] [Algebra R K]
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    [hprime : (RingHom.ker k.toRingHom).IsPrime]
    (hlifts : ∀ (v : ℕ)
      (f : MvPolynomial (Fin v) R →ₐ[R]
        MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
          (originalNormalizedHypersurfacePolynomial312 r j) i)
      (hf : Function.Surjective f),
      OriginalPolynomialPhysicalTestLifts317 R n r hr j hn i f hf (RingHom.ker k.toRingHom)) :
    ∃ q : PrimeSpectrum (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i),
      q.asIdeal = RingHom.ker k.toRingHom ∧
      monomialClosedCoefficientChartToLocus312 R 3 n
          (originalNormalizedHypersurfacePolynomial312 r j) i q ∈
        monomialPolynomialContainmentSmoothOpen312 R 3 n
          (originalNormalizedHypersurfacePolynomial312 r j) := by
  let A := MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
    (originalNormalizedHypersurfacePolynomial312 r j) i
  let q : PrimeSpectrum A := ⟨RingHom.ker k.toRingHom, hprime⟩
  letI : Algebra.FinitePresentation R A :=
    monomialPolynomialContainmentCoefficientAlgebra_finitePresentation312
      R 3 n (originalNormalizedHypersurfacePolynomial312 r j) i
  obtain ⟨v, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  have htests : OriginalPolynomialPhysicalTestLifts317 R n r hr j hn i f hf q.asIdeal :=
    hlifts v f hf
  exact ⟨q, rfl, originalCoefficient_memSmooth_of_physicalTests317
    R n r hr j hn i f hf q htests⟩

variable (R : Type u) [CommRing R] (r : MvPolynomial (Fin 4) R)
variable (hr : r.IsHomogeneous 3) (K : Type u) [Field K] [Algebra R K]
variable (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
local notation "pointDegree" => Scheme.Hom.residueDegree
  (hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K))) P.val
local notation "pointPositive" => originalClosedPoint_residueDegree_pos317 R r hr K P

/-- ORIGINAL closed point → an actual SAME coefficient chart and kernel prime
in the actual smooth open. No chart, family, diagram, lift or formal-smoothness
outcome is an input. The original field-family identity remains a conclusion. -/
lemma originalClosedPoint_coefficientChart_memSmooth_exists317
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :
    ∃ (j : Fin 4) (i : MonomialCoefficientChartIndex300 3 pointDegree)
      (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree
        (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
      (hk : Function.Surjective k),
      (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
        ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker ∧
      ∃ q : PrimeSpectrum (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree
          (originalNormalizedHypersurfacePolynomial312 r j) i),
        q.asIdeal = RingHom.ker k.toRingHom ∧
        monomialClosedCoefficientChartToLocus312 R 3 pointDegree
            (originalNormalizedHypersurfacePolynomial312 r j) i q ∈
          monomialPolynomialContainmentSmoothOpen312 R 3 pointDegree
            (originalNormalizedHypersurfacePolynomial312 r j) := by
  obtain ⟨j, i, k, hk, hpoint, hphysical⟩ :=
    originalClosedPoint_canonicalTests_physicalLift317 R r hr K P hK0 hRK
  letI : (RingHom.ker k.toRingHom).IsPrime := RingHom.ker_isPrime k.toRingHom
  have hall : ∀ (v : ℕ)
      (f : MvPolynomial (Fin v) R →ₐ[R]
        MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree
          (originalNormalizedHypersurfacePolynomial312 r j) i)
      (hf : Function.Surjective f),
      OriginalPolynomialPhysicalTestLifts317 R pointDegree r hr j pointPositive i f hf
        (RingHom.ker k.toRingHom) := by
    intro v f hf N hN
    exact hphysical v f hf (RingHom.ker k.toRingHom) rfl N hN
  exact ⟨j, i, k, hk, hpoint,
    originalKernelPoint_memSmooth_of_allPhysicalPresentations317
      R pointDegree r hr j pointPositive i K k hall⟩

end PfaffianDescent
end

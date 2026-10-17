import PfaffianDescent.OriginalNormalizedPolynomialGlobalHilbertSmoothMap
import PfaffianDescent.OriginalHilbertCompleteLocalLift317
import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterGluedFinitePresentation

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The actual field-valued coefficient map sends the closed point to its
original kernel prime; this bounded equality precedes all global aliases. -/
private theorem globalCoefficientFieldPoint_eq_kernel001
    {C K : Type u} [CommRing C] [Field K] (k : C →+* K)
    (q : PrimeSpectrum C) (hq : q.asIdeal = RingHom.ker k) :
    Spec.map (CommRingCat.ofHom k) (IsLocalRing.closedPoint K) = q := by
  apply PrimeSpectrum.ext
  change (PrimeSpectrum.comap k (IsLocalRing.closedPoint K)).asIdeal = q.asIdeal
  exact (AllCharacteristics.fieldPoint_asIdeal_eq_ker k).trans hq.symm

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d)
variable (j : Fin 4) (n : ℕ) (hn : 0 < n)

/-- Derive exact global LFP locally before any smooth-locus header is
formed; no global LFP or smooth-point premise is added. -/
private theorem originalClosedPointGlobalHilbertObject_lfp001 :
    LocallyOfFinitePresentation (originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn).hom :=
  originalPositiveHomogeneousParameterGluedToBase_locallyOfFinitePresentation001
    (equationIdeal p hp) n hn

attribute [local instance] originalClosedPointGlobalHilbertObject_lfp001

variable {K : Type u} [Field K] [Algebra R K]
variable (i : MonomialCoefficientChartIndex300 3 n)
variable (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
  (originalNormalizedHypersurfacePolynomial312 p j) i →ₐ[R] K)

/-- Actual original coefficient field classifier, followed by the exact
constructed local312-to-global map. No global field point is supplied. -/
def originalCoefficientTestGlobalClassifyingMap001 :
    originalNormalizedAffineTest317 R K ⟶
      originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn :=
  originalCoefficientTestClassifyingMap317 R 3 n
    (originalNormalizedHypersurfacePolynomial312 p j) i k ≫
      originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn

/-- Local317 coefficient membership places this constructed field point
in the genuine GLOBAL smooth locus. The natural original-point caller
below derives its local membership internally from accepted317. -/
theorem originalCoefficientTestGlobalClassifyingMap_mem_smoothLocus001
    (q : PrimeSpectrum (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) i))
    (hq : q.asIdeal = RingHom.ker k.toRingHom)
    (hsm : monomialClosedCoefficientChartToLocus312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j) i q ∈
      monomialPolynomialContainmentSmoothOpen312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j)) :
    (originalCoefficientTestGlobalClassifyingMap001 p hp j n hn i k).left
      (IsLocalRing.closedPoint K) ∈
        (originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn).hom.smoothLocus := by
  have hLocal :
      (originalCoefficientTestClassifyingMap317 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j) i k).left
          (IsLocalRing.closedPoint K) ∈
      monomialPolynomialContainmentSmoothOpen312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j) := by
    change monomialClosedCoefficientChartToLocus312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) i
      (Spec.map (CommRingCat.ofHom k.toRingHom) (IsLocalRing.closedPoint K)) ∈ _
    rw [globalCoefficientFieldPoint_eq_kernel001 k.toRingHom q hq]
    exact hsm
  change (originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn).left
    ((originalCoefficientTestClassifyingMap317 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) i k).left
        (IsLocalRing.closedPoint K)) ∈ _
  exact originalNormalizedPolynomialGlobalHilbertMap_mem_smoothLocus001
    p hp j n hn _ hLocal

/-- The actual317 complete-local lift produces local and GLOBAL classifier
maps, with the global map literally their constructed composition. Both
original reduction identities are derived, not added as lift premises. -/
theorem originalCoefficientTestGlobalClassifyingMap_completeAlgebraLift001
    {A : Type u} [CommRing A] [Algebra R A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (b : A →ₐ[R] K) (hb : Function.Surjective b)
    (q : PrimeSpectrum (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) i))
    (hq : q.asIdeal = RingHom.ker k.toRingHom)
    (hsm : monomialClosedCoefficientChartToLocus312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j) i q ∈
      monomialPolynomialContainmentSmoothOpen312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 p j)) :
    ∃ (cLocal : originalNormalizedAffineTest317 R A ⟶
        monomialPolynomialContainmentRepresentingObject312 R 3 n
          (originalNormalizedHypersurfacePolynomial312 p j))
      (cGlobal : originalNormalizedAffineTest317 R A ⟶
        originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn),
      cGlobal = cLocal ≫ originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn ∧
      originalNormalizedAffineTestMap317 R b ≫ cLocal =
        originalCoefficientTestClassifyingMap317 R 3 n
          (originalNormalizedHypersurfacePolynomial312 p j) i k ∧
      originalNormalizedAffineTestMap317 R b ≫ cGlobal =
        originalCoefficientTestGlobalClassifyingMap001 p hp j n hn i k := by
  obtain ⟨cLocal, hLocal⟩ := originalHilbertCoefficientSmoothPoint_classifierLift317 R b hb
    3 n (originalNormalizedHypersurfacePolynomial312 p j) i k q hq hsm
  refine ⟨cLocal, cLocal ≫ originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn,
    rfl, hLocal, ?_⟩
  change originalNormalizedAffineTestMap317 R b ≫
      (cLocal ≫ originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn) =
    originalCoefficientTestClassifyingMap317 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) i k ≫
        originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn
  rw [← Category.assoc, hLocal]

section OriginalPoint
variable (R : Type u) [CommRing R] (r : MvPolynomial (Fin 4) R)
  (hr : r.IsHomogeneous 3) (K : Type u) [Field K] [Algebra R K]
  (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
local notation "pointDegree" => Scheme.Hom.residueDegree
  (hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K))) P.val
local notation "pointPositive" => originalClosedPoint_residueDegree_pos317 R r hr K P

/-- ORIGINAL smooth cubic/closed point constructs a GLOBAL smooth field
classifier and its specified complete-local algebra lift. The SAME original
j/i/k seed, whole-point kernel identity and both classifier reductions are
retained. No selected chart/point/classifier, global smooth membership, lift,
family or matching outcome is an input. Whole-family extraction is separate. -/
theorem originalClosedPoint_globalHilbertSmoothClassifierLift_completeAlgebra001
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K))
    {A : Type u} [CommRing A] [Algebra R A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (b : A →ₐ[R] K) (hb : Function.Surjective b) :
    ∃ (j : Fin 4) (i : MonomialCoefficientChartIndex300 3 pointDegree)
      (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree
        (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
      (hk : Function.Surjective k),
      (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
        ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker ∧
      (originalCoefficientTestGlobalClassifyingMap001 r hr j pointDegree pointPositive i k).left
        (IsLocalRing.closedPoint K) ∈
          (originalNormalizedPolynomialGlobalHilbertObject001 r hr pointDegree pointPositive).hom.smoothLocus ∧
      ∃ (cLocal : originalNormalizedAffineTest317 R A ⟶
          monomialPolynomialContainmentRepresentingObject312 R 3 pointDegree
            (originalNormalizedHypersurfacePolynomial312 r j))
        (cGlobal : originalNormalizedAffineTest317 R A ⟶
          originalNormalizedPolynomialGlobalHilbertObject001 r hr pointDegree pointPositive),
        cGlobal = cLocal ≫ originalNormalizedPolynomialGlobalHilbertMap001 r hr j pointDegree pointPositive ∧
        originalNormalizedAffineTestMap317 R b ≫ cLocal =
          originalCoefficientTestClassifyingMap317 R 3 pointDegree
            (originalNormalizedHypersurfacePolynomial312 r j) i k ∧
        originalNormalizedAffineTestMap317 R b ≫ cGlobal =
          originalCoefficientTestGlobalClassifyingMap001 r hr j pointDegree pointPositive i k := by
  obtain ⟨j, i, k, hk, hPoint, q, hq, hsm⟩ :=
    originalClosedPoint_coefficientChart_memSmooth_exists317 R r hr K P hK0 hRK
  refine ⟨j, i, k, hk, hPoint, ?_, ?_⟩
  · exact originalCoefficientTestGlobalClassifyingMap_mem_smoothLocus001
      r hr j pointDegree pointPositive i k q hq hsm
  · exact originalCoefficientTestGlobalClassifyingMap_completeAlgebraLift001
      r hr j pointDegree pointPositive i k b hb q hq hsm
end OriginalPoint

end PfaffianDescent
end

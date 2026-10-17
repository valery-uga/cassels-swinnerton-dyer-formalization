import PfaffianDescent.CorayActualSelectedComponentDegreePositivity
import PfaffianDescent.CorayJointStabilizerComponentDegreeBound
import PfaffianDescent.CorayJointGeometricComponentModel

/-! SAME actual L/C/M/D: all-field GI, original-K field degree = geometric r,
and POSITIVE OWN descended component degree = geometric μ with r*μ≤3n. All equations,
component choices and field/curve degrees remain literal. SOURCE ONLY /
UNVERIFIED; root owns compiler/audit. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- From ORIGINAL smooth cubic/q and the actual original selected prime,
and genuine original minimality, construct ONCE a model of the actual chosen geometric component. That SAME
model is all-field geometrically integral, has original-K field degree equal
to the actual geometric component count, and OWN coordinate degree equal to
the geometric component's OWN degree. Their product is derived ≤3n. -/
theorem originalMinimalGeometricComponent_exists_jointModel_positive_degree_bound
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsAlgClosed Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω))
    (hP : P.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    ∃ (L : FiniteGaloisIntermediateField K Ω)
      (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L)),
      C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes ∧
        C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = P.toIdeal ∧
        let M := homogeneousIdealStabilizerFixedField (K := K) C
        let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
        D.toIdeal.IsPrime ∧
          D.toIdeal.map (MvPolynomial.map (algebraMap M L)) = C.toIdeal ∧
          Module.finrank K M = Nat.card (irreducibleComponents
            (scheme (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) ∧
          GeometricallyIntegral (toBase D) ∧
          (∀ (T : Type u) [Field T] [Algebra M T],
            let DT := D.map (componentPolynomialCoefficientMap (algebraMap M T))
            DT.toIdeal.IsPrime ∧ IsIntegral (scheme DT) ∧
              IsIntegral (CategoryTheory.Limits.pullback (toBase D)
                (Spec.map (CommRingCat.ofHom (algebraMap M T))))) ∧
          actualCurveCoordinateHilbertDegree D = actualCurveCoordinateHilbertDegree P ∧
          0 < actualCurveCoordinateHilbertDegree D ∧
          Module.finrank K M * actualCurveCoordinateHilbertDegree D ≤ 3 * n := by
  classical
  letI : I.toIdeal.IsPrime := hI.isPrime
  have hIrel := selectedProjectiveMinimalComponent_homogeneous_relevant
    p q hp hp0 n hq hnot I hI
  obtain ⟨L, C, hCmin, hCext, hDprime, hDL, hfield, hGI, hall, hDP, hproduct⟩ :=
    originalSelectedGeometricComponent_exists_jointModel_degree_bound
      p q hp hp0 n hn hq hnot I hIrel hI.le P hP
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  let f := algebraMap K Ω
  have hmapinj : Function.Injective (MvPolynomial.map f :
      MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) Ω) :=
    MvPolynomial.map_injective f (FaithfulSMul.algebraMap_injective K Ω)
  have hpΩ0 : p.map f ≠ 0 := by
    intro h
    apply hp0
    exact hmapinj (by simpa using h)
  letI : Smooth (hypersurfaceToBase (p.map f) (hp.map f)) :=
    smooth_hypersurfaceToBase_map f p hp
  have hmapSpan : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map
      (MvPolynomial.map f) = Ideal.span ({p.map f} : Set (MvPolynomial (Fin 4) Ω)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hnotΩ : q.map f ∉ Ideal.span ({p.map f} : Set (MvPolynomial (Fin 4) Ω)) := by
    intro h
    have hm : q ∈ Ideal.comap (MvPolynomial.map f)
        ((Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map (MvPolynomial.map f)) := by
      change q.map f ∈ (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map
        (MvPolynomial.map f)
      rw [hmapSpan]
      exact h
    have hcontract : Ideal.comap (MvPolynomial.map f)
        ((Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map (MvPolynomial.map f)) =
          Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) :=
      mvPolynomial_comap_map_coefficientExtension (k := K) (K := Ω)
        (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    rw [hcontract] at hm
    exact hnot hm
  have hmapPQ : (projectiveIntersectionIdeal p q hp hq).toIdeal.map (MvPolynomial.map f) =
      (projectiveIntersectionIdeal (p.map f) (q.map f) (hp.map f) (hq.map f)).toIdeal := by
    rw [projectiveIntersectionIdeal_toIdeal, projectiveIntersectionIdeal_toIdeal,
      Ideal.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton]
  have hPwhole : P.toIdeal ∈
      ((projectiveIntersectionIdeal p q hp hq).toIdeal.map (MvPolynomial.map f)).minimalPrimes :=
    originalMinimalPrime_coefficientExtension_minimalPrime_over_wholeIdeal
      (projectiveIntersectionIdeal p q hp hq).toIdeal I.toIdeal hI P.toIdeal hP
  have hPΩ : P.toIdeal ∈ (projectiveIntersectionIdeal
      (p.map f) (q.map f) (hp.map f) (hq.map f)).toIdeal.minimalPrimes := by
    rw [← hmapPQ]
    exact hPwhole
  have hposP : 0 < actualCurveCoordinateHilbertDegree P :=
    selectedProjectiveMinimalComponent_hilbertDegree_pos
      (p.map f) (q.map f) (hp.map f) hpΩ0 n (hq.map f) hnotΩ P hPΩ
  have hposD : 0 < actualCurveCoordinateHilbertDegree D := by
    rw [hDP]
    exact hposP
  exact ⟨L, C, hCmin, hCext, hDprime, hDL, hfield, hGI, hall, hDP, hposD, hproduct⟩

end PfaffianDescent.Coray

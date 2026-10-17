import PfaffianDescent.CorayOriginalEquationsGeometricDegreeBound
import PfaffianDescent.CorayJointGeometricComponentModel

/-! SAME actual L/C/M/D: all-field GI, original-K field degree = geometric r,
and OWN descended component degree = geometric μ with r*μ≤3n. All equations,
component choices and field/curve degrees remain literal. SOURCE ONLY /
UNVERIFIED; root owns compiler/audit. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- From ORIGINAL smooth cubic/q and the actual original selected prime,
construct ONCE a model of the actual chosen geometric component. That SAME
model is all-field geometrically integral, has original-K field degree equal
to the actual geometric component count, and OWN coordinate degree equal to
the geometric component's OWN degree. Their product is derived ≤3n. -/
theorem originalSelectedGeometricComponent_exists_jointModel_degree_bound
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsAlgClosed Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (hPQI : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ I.toIdeal)
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
          Module.finrank K M * actualCurveCoordinateHilbertDegree D ≤ 3 * n := by
  classical
  obtain ⟨L, C, hCmin, hCext, hDprime, hDL, hfield, hGI, hall⟩ :=
    originalGeometricMinimalPrime_exists_jointStabilizerModel I hIrel P.toIdeal hP
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  have hPC : actualCurveCoordinateHilbertDegree P = actualCurveCoordinateHilbertDegree C :=
    actualCurveCoordinateHilbertDegree_eq_coefficientExtension C P hCext
  have hCD : actualCurveCoordinateHilbertDegree C = actualCurveCoordinateHilbertDegree D :=
    actualCurveCoordinateHilbertDegree_eq_coefficientExtension D C hDL
  have hDP : actualCurveCoordinateHilbertDegree D = actualCurveCoordinateHilbertDegree P :=
    (hPC.trans hCD).symm
  have hbound := originalSelectedPrime_geometricComponents_card_mul_degree_bound
    p q hp hp0 n hn hq hnot I hIrel hPQI P hP
  have hproduct : Module.finrank K M * actualCurveCoordinateHilbertDegree D ≤ 3 * n := by
    rw [hfield, hDP]
    exact hbound
  exact ⟨L, C, hCmin, hCext, hDprime, hDL, hfield, hGI, hall, hDP, hproduct⟩

end PfaffianDescent.Coray

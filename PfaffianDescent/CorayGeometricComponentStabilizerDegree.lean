import PfaffianDescent.CorayActualMinimalPrimeSplitting
import PfaffianDescent.CorayMinimalPrimeOrbitCount

/-!
# Actual geometric component count and original-K stabilizer-field degree

The finite Galois splitting field and selected component are constructed from
an ACTUAL original Ω-minimal prime. The derived native minimal-prime/projective
component bijection identifies the geometric count. No arbitrary finite-field
count is declared to be Coray's r; the constructed splitting equivalence proves
that identification. SOURCE ONLY / UNVERIFIED: root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Construct the ACTUAL finite-field component over an original geometric
minimal prime, its whole stabilizer-field descent, and identify the degree of
that ACTUAL fixed field over ORIGINAL K with the ACTUAL number of projective
irreducible components over Ω. Every count, field and descent is derived. -/
theorem originalGeometricMinimalPrime_exists_stabilizerModel_finrank_eq_geometricComponents_card
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsAlgClosed Ω]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (P : Ideal (MvPolynomial (Fin 4) Ω))
    (hP : P ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    ∃ (L : FiniteGaloisIntermediateField K Ω)
      (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L)),
      C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes ∧
        C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = P ∧
        let M := homogeneousIdealStabilizerFixedField (K := K) C
        let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
        D.toIdeal.IsPrime ∧
          D.toIdeal.map (MvPolynomial.map (algebraMap M L)) = C.toIdeal ∧
          Module.finrank K M = Nat.card (irreducibleComponents
            (scheme (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) := by
  classical
  obtain ⟨L, e, he, hmap⟩ := originalHomogeneousIdeal_exists_finiteGalois_minimalPrimeSplitting
    (Ω := Ω) I
  let JΩ := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  let JL := I.map (componentPolynomialCoefficientMap (algebraMap K L))
  let p : JΩ.toIdeal.minimalPrimes := ⟨P, hP⟩
  let C := (e p).1.homogeneousCore (homogeneousSubmodule (Fin 4) L)
  have hCeq : C.toIdeal = (e p).1 :=
    homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal JL (e p).1 (e p).2
  have hCmin : C.toIdeal ∈ JL.toIdeal.minimalPrimes := by
    rw [hCeq]
    exact (e p).2
  have hCext : C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = P := by
    rw [hCeq]
    exact hmap p
  letI : C.toIdeal.IsPrime := hCmin.1.1
  have hdesc := homogeneousPrime_stabilizerFixedField_descends (K := K) C
  have hdegree : Module.finrank K (homogeneousIdealStabilizerFixedField (K := K) C) =
      Nat.card JL.toIdeal.minimalPrimes :=
    homogeneousMinimalPrime_stabilizerFixedField_finrank_eq_minimalPrimes_card
      I.toIdeal C hCmin
  have hsplitCard : Nat.card JL.toIdeal.minimalPrimes = Nat.card JΩ.toIdeal.minimalPrimes :=
    Nat.card_congr e.symm
  have hgeometricCard : Nat.card JΩ.toIdeal.minimalPrimes =
      Nat.card (irreducibleComponents (scheme JΩ)) :=
    Nat.card_congr (homogeneousCoefficientExtension_minimalPrimesEquivProjectiveComponents
      (E := Ω) I hIrel)
  exact ⟨L, C, hCmin, hCext, hdesc.1, hdesc.2,
    hdegree.trans (hsplitCard.trans hgeometricCard)⟩

end PfaffianDescent.Coray

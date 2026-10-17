import PfaffianDescent.CorayOriginalClosedPointResidueEmbedding
import PfaffianDescent.CorayLiteralIncidenceComponentCount

/-! Future join: construct the missing actual original residue embedding,
then apply the exact SAME component-count5 producer, with no count premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Construct ψ for SAME original P; then the SAME actual geometric minimal
G constructs its joint stabilizer model and whole incidence whose native
rank counts the components through the literal ψ-induced original-P lift. -/
theorem originalGeometricMinimalPrime_exists_jointModel_entireIncidence_componentCount_and_residueEmbedding
    [CharZero K] [IsGalois K Ω]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ I)
    (G : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) Ω))
    (hG : G.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes)
    (P : closedPoints (scheme I)) :
    letI := pointAlgebra (toBase I) P.1
    ∃ psi : (scheme I).residueField P.1 →ₐ[K] Ω,
      Function.Injective psi ∧
    ∃ (L : FiniteGaloisIntermediateField K Ω)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L)),
      ∃ hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes,
      ∃ hCG : C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = G.toIdeal,
      let M := homogeneousIdealStabilizerFixedField (K := K) C
      let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
      let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
      let ep := (scheme I).fromSpecResidueField P.1
      let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
      letI := pointAlgebra (toBase I) P.1
      let v := Spec.map (CommRingCat.ofHom psi.toRingHom)
      let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
      ∃ hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal,
      ∃ hfinite : IsFinite (pullback.fst ep (coefficientComponentToOriginal I D hID)),
      ∃ hv : v ≫ ep ≫ toBase I = b,
        letI := hfinite
        let q := nativeOriginalPointGeometricLift ep (toBase I) b v hv ≫ iO.inv
        GeometricallyIntegral (toBase D) ∧
          finiteSchemeRank (pullback.fst ep (coefficientComponentToOriginal I D hID)) =
            Nat.card {T : irreducibleComponents (scheme IO) | q (IsLocalRing.closedPoint Ω) ∈ T.1} := by
  letI := pointAlgebra (toBase I) P.1
  obtain ⟨psi, hinj⟩ := originalProjectiveClosedPoint_exists_residueAlgEmbedding
    (Ω := Ω) I P
  exact ⟨psi, hinj,
    originalGeometricMinimalPrime_exists_jointModel_entireIncidence_componentCount
      I hIrel G hG P psi⟩

end PfaffianDescent.Coray

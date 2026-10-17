import PfaffianDescent.CorayOriginalStabilizerModelNativeGenericIsomorphismDescent
import PfaffianDescent.CorayUnitCokernelIsomorphismOpenSupport

/-! SAME fixed whole-stabilizer model: actual finite closed support for the
literal native unit-cokernel, derived from the constructed isomorphism locus. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Derive finite closed support of the literal unit cokernel for the SAME
actual original selected I and WHOLE stabilizer model C/M/D/f. No support,
isomorphism-locus, birationality or quotient-finiteness input is supplied. -/
theorem selectedOriginalPrime_fixedStabilizerModel_unitCokernel_exists_finiteClosedSupport001
    {K L Ω : Type u} [Field K] [CharZero K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [FiniteDimensional K L] [IsGalois K L] [IsAlgClosed Ω] [IsGalois K Ω]
    [Algebra.IsAlgebraic K Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes)
    (hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap L Ω))).IsPrime) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    ∃ hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal,
      let f := coefficientComponentToOriginal I D hID
      let Q := cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      ∃ S : Set (scheme I), ∃ hS : IsClosed S,
        S.Finite ∧ (∀ x ∈ S, IsClosed ({x} : Set (scheme I))) ∧
          schemeModuleStalkSupport Q ⊆ S := by
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  obtain ⟨hID, S, hS, hFinite, hPoints, hIso⟩ :=
    selectedOriginalPrime_stabilizerModel_exists_finiteClosedBadSet_restriction_isIso001
      p q hp hp0 n hq hnot I hI hIrel C hC hCO
  let f := coefficientComponentToOriginal I D hID
  let U : (scheme I).Opens := ⟨Sᶜ, hS.isOpen_compl⟩
  letI : IsIso (f ∣_ U) := hIso
  have hSupport : schemeModuleStalkSupport
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ⊆ S := by
    have h := unitCokernelSheaf_stalkSupport_subset_compl_of_restrict_isIso f U
    change schemeModuleStalkSupport
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ⊆ (Sᶜ)ᶜ at h
    simpa only [compl_compl] using h
  exact ⟨hID, S, hS, hFinite, hPoints, hSupport⟩

end PfaffianDescent.Coray

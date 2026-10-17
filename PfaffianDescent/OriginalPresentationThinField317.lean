import PfaffianDescent.OriginalClassifyingFieldStalk317
import PfaffianDescent.NativePolynomialChartArtinianCriterion316
import PfaffianDescent.NativeArtinianTestResidue316

/-! SOURCE ONLY317. Canonical thin polynomial Artinian tests map to the
ORIGINAL field with exactly the original classifying map on A. No arbitrary
fibre lifting assumption or replacement of that field is introduced. -/
noncomputable section
namespace PfaffianDescent
open IsLocalRing

variable {R A K : Type*} [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra R K]
  {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] A) (hf : Function.Surjective f)
  (q : Ideal A) [q.IsPrime] (k : A →ₐ[R] K)
  (hq : RingHom.ker k.toRingHom = q) (hk : Function.Surjective k)
local notation "P" => Localization.AtPrime (q.comap f.toRingHom)
local notation "I" => RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
local notation "m" => maximalIdeal P

/-- The actual localized presentation maps to the original point's field. -/
def originalPresentationFieldMap317 : P →ₐ[R] K :=
  (originalClassifyingFieldStalkMap317 q k hq).comp
    (localSurjectivePresentationMap316 f q)

lemma originalPresentationFieldMap_algebraMap317 (x : MvPolynomial (Fin v) R) :
    originalPresentationFieldMap317 f q k hq
      (algebraMap (MvPolynomial (Fin v) R) P x) = k (f x) :=
  (congrArg (originalClassifyingFieldStalkMap317 q k hq)
    (localSurjectivePresentationMap_algebraMap316 f q x)).trans
      (originalClassifyingFieldStalkMap_algebraMap317 q k hq (f x))

include hf hk in
lemma originalPresentationFieldMap_surjective317 :
    Function.Surjective (originalPresentationFieldMap317 f q k hq) :=
  (originalClassifyingFieldStalkMap_surjective317 q k hq hk).comp
    (localSurjectivePresentationMap_surjective316 f hf q)

include hf hk in
lemma originalPresentationFieldMap_kernel317 :
    RingHom.ker (originalPresentationFieldMap317 f q k hq).toRingHom = m :=
  IsLocalRing.ker_eq_maximalIdeal _
    (originalPresentationFieldMap_surjective317 f hf q k hq hk)

include hf hk in
private lemma originalPresentationThinField_kernelBound317 (N : ℕ) (hN : 0 < N) :
    obstructionThinIdeal316 m I N ≤
      RingHom.ker (originalPresentationFieldMap317 f q k hq).toRingHom := by
  rw [originalPresentationFieldMap_kernel317 f hf q k hq hk]
  exact obstructionThinIdeal_le_maximal316 I
    (localPolynomialPresentation_kernel_le_maximal316 f q) N hN

/-- Genuine scalar-preserving quotient map to the ORIGINAL residue field. -/
def originalPresentationThinFieldMap317 (N : ℕ) (hN : 0 < N) :
    P ⧸ obstructionThinIdeal316 m I N →ₐ[R] K :=
  Ideal.Quotient.liftₐ _ (originalPresentationFieldMap317 f q k hq)
    (fun _ hx => RingHom.mem_ker.mp
      (originalPresentationThinField_kernelBound317 f hf q k hq hk N hN hx))

lemma originalPresentationThinFieldMap_mk317 (N : ℕ) (hN : 0 < N) (x : P) :
    originalPresentationThinFieldMap317 f hf q k hq hk N hN
      (Ideal.Quotient.mk (obstructionThinIdeal316 m I N) x) =
        originalPresentationFieldMap317 f q k hq x := rfl

lemma originalPresentationThinFieldMap_surjective317 (N : ℕ) (hN : 0 < N) :
    Function.Surjective (originalPresentationThinFieldMap317 f hf q k hq hk N hN) := by
  intro x
  obtain ⟨a, ha⟩ := originalPresentationFieldMap_surjective317 f hf q k hq hk x
  exact ⟨Ideal.Quotient.mk (obstructionThinIdeal316 m I N) a,
    (originalPresentationThinFieldMap_mk317 f hf q k hq hk N hN a).trans ha⟩

/-- Concrete chart tests agree on polynomial representatives BEFORE using
surjectivity to compare them on every original chart element. -/
lemma localPolynomialArtinianChartTest_polynomial317 (N : ℕ) (x : MvPolynomial (Fin v) R) :
    localPolynomialArtinianChartTest316 f hf q N (f x) =
      Ideal.Quotient.mk (obstructionThinIdeal316 m I N)
        (algebraMap (MvPolynomial (Fin v) R) P x) := by
  have hbound : I ≤ obstructionThinIdeal316 m I N := le_sup_left
  change Ideal.Quotient.factorₐ R hbound
    ((localPolynomialPresentationQuotientEquiv316 f hf q).symm
      (algebraMap A (Localization.AtPrime q) (f x))) = _
  have hlocal := localSurjectivePresentationMap_algebraMap316 f q x
  have heq : (localPolynomialPresentationQuotientEquiv316 f hf q).symm
      (algebraMap A (Localization.AtPrime q) (f x)) =
      Ideal.Quotient.mk I (algebraMap (MvPolynomial (Fin v) R) P x) := by
    rw [← hlocal]
    exact Ideal.quotientKerAlgEquivOfSurjective_symm_apply
      (localSurjectivePresentationMap_surjective316 f hf q)
      (algebraMap (MvPolynomial (Fin v) R) P x)
  exact (congrArg (Ideal.Quotient.factorₐ R hbound) heq).trans
    (Ideal.Quotient.factorₐ_apply_mk R hbound (algebraMap (MvPolynomial (Fin v) R) P x))

lemma originalPresentationThinFieldMap_chartTest317 (N : ℕ) (hN : 0 < N) :
    (originalPresentationThinFieldMap317 f hf q k hq hk N hN).comp
      (localPolynomialArtinianChartTest316 f hf q N) = k := by
  apply AlgHom.ext
  intro a
  obtain ⟨x, rfl⟩ := hf a
  change originalPresentationThinFieldMap317 f hf q k hq hk N hN
    (localPolynomialArtinianChartTest316 f hf q N (f x)) = k (f x)
  rw [localPolynomialArtinianChartTest_polynomial317 f hf q N x,
    originalPresentationThinFieldMap_mk317]
  exact originalPresentationFieldMap_algebraMap317 f q k hq x

end PfaffianDescent
end

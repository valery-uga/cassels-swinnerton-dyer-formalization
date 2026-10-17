import PfaffianDescent.OriginalCoefficientProjectiveFamily317
import PfaffianDescent.OriginalPresentationThinField317

/-! Actual local polynomial Artinian test families specialize over their
constructed map to the original field, with equality of whole ideals. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IsLocalRing
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (n : ℕ)
  (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d)
  (j : Fin 4) (hn : 0 < n) (i : MonomialCoefficientChartIndex300 3 n)
variable {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n (originalNormalizedHypersurfacePolynomial312 r j) i)) (hf : Function.Surjective f)
  (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
local notation "P" => Localization.AtPrime (q.comap f.toRingHom)
local notation "I" => RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
local notation "m" => maximalIdeal P
local notation "S" => fun N : ℕ => P ⧸ obstructionThinIdeal316 m I N

def originalThinCoefficientProjectiveFamily317 (N : ℕ) :
    FiniteFlatHilbertPoint195
      (hypersurfaceToBase (r.map (algebraMap R (S N))) (hr.map (algebraMap R (S N)))) n :=
  originalCoefficientTestProjectiveFamily317 R n r hr j hn i
    (localPolynomialArtinianChartTest316 f hf q N)

lemma originalThinCoefficientProjectiveFamily_fieldIdeal317
    {K : Type u} [Field K] [Algebra R K] (k : (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n (originalNormalizedHypersurfacePolynomial312 r j) i) →ₐ[R] K)
    (hq : RingHom.ker k.toRingHom = q) (hk : Function.Surjective k)
    (N : ℕ) (hN : 0 < N) :
    (originalThinCoefficientProjectiveFamily317 R n r hr j hn i f hf q N).val.comap
      (hypersurfaceReductionMap
        (originalPresentationThinFieldMap317 f hf q k hq hk N hN).toRingHom
        (r.map (algebraMap R (S N))) (hr.map (algebraMap R (S N)))
        (r.map (algebraMap R K)) (hr.map (algebraMap R K))
        (originalNormalizedTestEquation317 R
          (originalPresentationThinFieldMap317 f hf q k hq hk N hN) r)) =
      (originalCoefficientTestProjectiveFamily317 R n r hr j hn i k).val :=
  (originalCoefficientTestProjectiveFamily_reductionWholeIdeal317 R n r hr j hn i
    (localPolynomialArtinianChartTest316 f hf q N)
    (originalPresentationThinFieldMap317 f hf q k hq hk N hN)).trans
      (congrArg (fun k => (originalCoefficientTestProjectiveFamily317 R n r hr j hn i k).val)
        (originalPresentationThinFieldMap_chartTest317 f hf q k hq hk N hN))

end PfaffianDescent
end

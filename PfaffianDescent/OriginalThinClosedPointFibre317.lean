import PfaffianDescent.OriginalThinProjectiveTestFamily317
import PfaffianDescent.OriginalClosedPointCoefficientChart317
import PfaffianDescent.NativeOriginalClosedPointFibre317

/-! Construct physical fibre squares of the canonical Artinian test families.
The final existence theorem derives its field-family identification from the
original closed point rather than adding that identification as an assumption. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
local instance thinOriginalClosedPointChartOpen317
    {A : Type u} [CommRing A] (p : MvPolynomial (Fin 4) A)
    {e : ℕ} (hp : p.IsHomogeneous e) (j : Fin 4) :
    IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 p hp j) :=
  originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 p hp j

variable (R : Type u) [CommRing R] (r : MvPolynomial (Fin 4) R)
  {d : ℕ} (hr : r.IsHomogeneous d) (K : Type u) [Field K] [Algebra R K]
  (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
  (j : Fin 4)

lemma originalThinProjectiveTest_fibre_of_fieldIdeal317
    (n : ℕ) (hn : 0 < n) (i : MonomialCoefficientChartIndex300 3 n)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R n r hr j hn i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R]
      MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i) (hf : Function.Surjective f)
    (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :
    ∃ u0 : Spec ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).residueField P.val) ⟶
      (originalThinCoefficientProjectiveFamily317 R n r hr j hn i f hf q N).val.subscheme,
      IsPullback u0
        ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val)
        (originalThinCoefficientProjectiveFamily317 R n r hr j hn i f hf q N).val.subschemeι
        (hypersurfaceReductionMap
          (originalPresentationThinFieldMap317 f hf q k hq hk N hN).toRingHom
          (r.map (algebraMap R (Localization.AtPrime (q.comap f.toRingHom) ⧸
        obstructionThinIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom)))
          (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N))) (hr.map (algebraMap R (Localization.AtPrime (q.comap f.toRingHom) ⧸
        obstructionThinIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom)))
          (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N)))
          (r.map (algebraMap R K)) (hr.map (algebraMap R K))
          (originalNormalizedTestEquation317 R
            (originalPresentationThinFieldMap317 f hf q k hq hk N hN) r)) := by
  have h := (originalThinCoefficientProjectiveFamily_fieldIdeal317 R n r hr j hn i
    f hf q k hq hk N hN).trans hpoint
  exact ⟨nativeOriginalClosedPointFibreMap317
    (originalThinCoefficientProjectiveFamily317 R n r hr j hn i f hf q N).val
    (hypersurfaceReductionMap
      (originalPresentationThinFieldMap317 f hf q k hq hk N hN).toRingHom
      (r.map (algebraMap R (Localization.AtPrime (q.comap f.toRingHom) ⧸
        obstructionThinIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom)))
          (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N))) (hr.map (algebraMap R (Localization.AtPrime (q.comap f.toRingHom) ⧸
        obstructionThinIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom)))
          (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N)))
      (r.map (algebraMap R K)) (hr.map (algebraMap R K))
      (originalNormalizedTestEquation317 R
        (originalPresentationThinFieldMap317 f hf q k hq hk N hN) r)) P h,
    nativeOriginalClosedPointFibreMap_isPullback317
    (originalThinCoefficientProjectiveFamily317 R n r hr j hn i f hf q N).val
    (hypersurfaceReductionMap
      (originalPresentationThinFieldMap317 f hf q k hq hk N hN).toRingHom
      (r.map (algebraMap R (Localization.AtPrime (q.comap f.toRingHom) ⧸
        obstructionThinIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom)))
          (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N))) (hr.map (algebraMap R (Localization.AtPrime (q.comap f.toRingHom) ⧸
        obstructionThinIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom)))
          (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N)))
      (r.map (algebraMap R K)) (hr.map (algebraMap R K))
      (originalNormalizedTestEquation317 R
        (originalPresentationThinFieldMap317 f hf q k hq hk N hN) r)) P h⟩

/-- All canonical thin test families have the original closed-point fibre.
The named predicate bounds elaboration before substituting the point's degree. -/
def OriginalCoefficientAllThinFibres317
    (n : ℕ) (hn : 0 < n) (i : MonomialCoefficientChartIndex300 3 n)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k) : Prop :=
  ∀ (v : ℕ) (f : MvPolynomial (Fin v) R →ₐ[R]
          MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
            (originalNormalizedHypersurfacePolynomial312 r j) i)
        (hf : Function.Surjective f)
        (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
          (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
        (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N),
        ∃ u0 : Spec ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).residueField P.val) ⟶
          (originalThinCoefficientProjectiveFamily317 R n r hr j
            hn i f hf q N).val.subscheme,
          IsPullback u0
            ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val)
            (originalThinCoefficientProjectiveFamily317 R n r hr j
              hn i f hf q N).val.subschemeι
            (hypersurfaceReductionMap
              (originalPresentationThinFieldMap317 f hf q k hq hk N hN).toRingHom
              (r.map (algebraMap R (Localization.AtPrime (q.comap f.toRingHom) ⧸
        obstructionThinIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom)))
          (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N))) (hr.map (algebraMap R (Localization.AtPrime (q.comap f.toRingHom) ⧸
        obstructionThinIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom)))
          (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N)))
              (r.map (algebraMap R K)) (hr.map (algebraMap R K))
              (originalNormalizedTestEquation317 R
                (originalPresentationThinFieldMap317 f hf q k hq hk N hN) r))

lemma originalCoefficient_allThinProjectiveTestFibres317
    (n : ℕ) (hn : 0 < n) (i : MonomialCoefficientChartIndex300 3 n)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R n r hr j hn i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker) :
    OriginalCoefficientAllThinFibres317 R r hr K P j n hn i k hk := by
  intro v f hf q hprime hq N hN
  exact originalThinProjectiveTest_fibre_of_fieldIdeal317 R r hr K P j n hn
    i k hk hpoint f hf q hq N hN

local notation "n" => Scheme.Hom.residueDegree
  (hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K))) P.val

lemma originalClosedPoint_allThinProjectiveTestFibres317
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (hRK : Function.Surjective (algebraMap R K)) :
    ∃ (i : MonomialCoefficientChartIndex300 3 n)
      (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
      (hk : Function.Surjective k),
      OriginalCoefficientAllThinFibres317 R r hr K P j n
        (originalClosedPoint_residueDegree_pos317 R r hr K P) i k hk := by
  obtain ⟨i, k, hk, hpoint⟩ :=
    originalClosedPoint_surjectiveCoefficientChart_exists317 R r hr K P j hP hRK
  exact ⟨i, k, hk, originalCoefficient_allThinProjectiveTestFibres317 R r hr K P j n
    (originalClosedPoint_residueDegree_pos317 R r hr K P) i k hk hpoint⟩

end PfaffianDescent
end

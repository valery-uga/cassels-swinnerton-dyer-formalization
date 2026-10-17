import PfaffianDescent.OriginalClosedPointNormalizedChartLift317
import PfaffianDescent.OriginalThinClosedPointFibre317
import PfaffianDescent.OriginalCoefficientProjectiveChartComap317
import AllCharacteristics.ProjectiveFiberSmoothness
import PfaffianDescent.OriginalPhysicalTestSmoothCriterion317

/-! SOURCE ONLY317. The canonical local polynomial thick/thin tests have
PHYSICAL normalized family lifts, constructed from the ORIGINAL smooth cubic
and ORIGINAL closed point. No lift, HZ or chart-membership outcome is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
local instance canonicalOriginalChartOpen317
    {A : Type u} [CommRing A] (p : MvPolynomial (Fin 4) A)
    {e : ℕ} (hp : p.IsHomogeneous e) (j : Fin 4) :
    IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 p hp j) :=
  originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 p hp j

section CanonicalPolynomialRings
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] A) (q : Ideal A) [q.IsPrime]
local notation "LP" => Localization.AtPrime (q.comap f.toRingHom)
local notation "Rel" => RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
local notation "mx" => maximalIdeal LP
local notation "Thick" => fun N : ℕ => LP ⧸ obstructionThickIdeal316 mx Rel N
local notation "Thin" => fun N : ℕ => LP ⧸ obstructionThinIdeal316 mx Rel N

private def canonicalPolynomialTestPi317 (N : ℕ) : Thick N →ₐ[R] Thin N :=
  Ideal.Quotient.factorₐ R (obstructionThickIdeal_le_thin316 mx Rel N)

private def canonicalPolynomialTestPiAlgebra317 (N : ℕ) : Algebra (Thick N) (Thin N) :=
  (canonicalPolynomialTestPi317 f q N).toRingHom.toAlgebra

private theorem canonicalPolynomialTestPiAlgebra_map317 (N : ℕ) :
    @algebraMap (Thick N) (Thin N) _ _ (canonicalPolynomialTestPiAlgebra317 f q N) =
      (canonicalPolynomialTestPi317 f q N).toRingHom := rfl

private theorem canonicalPolynomialTestPi_surjective317 (N : ℕ) :
    Function.Surjective (canonicalPolynomialTestPi317 f q N) :=
  obstructionQuotientReduction_surjective316 mx Rel N

private theorem canonicalPolynomialTestPi_kernel_sq_zero317 (N : ℕ) :
    (RingHom.ker (canonicalPolynomialTestPi317 f q N).toRingHom) ^ 2 = ⊥ :=
  obstructionQuotientReduction_kernel_sq_zero316 mx Rel N
    (localPolynomialPresentation_kernel_le_maximal316 f q)

private theorem canonicalPolynomialThin_localArtinian317 [IsNoetherianRing R]
    (N : ℕ) (hN : 0 < N) : IsLocalRing (Thin N) ∧ IsArtinianRing (Thin N) := by
  letI : IsNoetherianRing LP := localPolynomial_isNoetherianRing316 R v (q.comap f.toRingHom)
  exact obstructionThinQuotient_local_artinian316 Rel
    (localPolynomialPresentation_kernel_le_maximal316 f q) N hN
end CanonicalPolynomialRings

/-- Carry point membership through a DERIVED original chart reduction
square. Both actual chart maps remain intact; no upstairs membership premise. -/
private theorem canonicalChartReduction_mem317
    {Y0 Y X0 X : Scheme.{u}} (v : Y0 ⟶ Y) (a0 : Y0 ⟶ X0)
    (a : Y ⟶ X) (w : X0 ⟶ X) (h : v ≫ a = a0 ≫ w)
    (x : X0) (hx : x ∈ Set.range a0) : w x ∈ Set.range a := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨v y, ?_⟩
  exact (congrArg (fun t : Y0 ⟶ X => t y) h).trans (congrArg w hy)

/-- Preserve a SPECIFIED original thin equation before substituting the
canonical tests. Equality elimination connects the literal317 map-polynomial
interface without supplying a family lift or changing any actual chart map. -/
private theorem specifiedOriginalNormalizedChartLift317
    {B S K : Type u} [CommRing B] [CommRing S] [Field K]
    [Algebra B S] [IsArtinianRing S] [IsLocalRing S]
    (hBS : Function.Surjective (algebraMap B S))
    (hI : (RingHom.ker (algebraMap B S)) ^ 2 = ⊥)
    (r : MvPolynomial (Fin 4) B) (hr : r.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase r hr)]
    (s : MvPolynomial (Fin 4) S) (hs : s.IsHomogeneous 3)
    (heBS : r.map (algebraMap B S) = s)
    (b : S →+* K) (hb : Function.Surjective b)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (heSK : s.map b = p) (P : closedPoints (hypersurface p hp))
    (I0 : FiniteFlatHilbertPoint195 (hypersurfaceToBase s hs)
      ((hypersurfaceToBase p hp).residueDegree P.val))
    (u0 : Spec ((hypersurface p hp).residueField P.val) ⟶ I0.val.subscheme)
    (HZ : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.val)
      I0.val.subschemeι (hypersurfaceReductionMap b s hs p hp heSK))
    (j : Fin 4)
    (hx : hypersurfaceReductionMap (algebraMap B S) r hr s hs heBS
      (hypersurfaceReductionMap b s hs p hp heSK
        (((hypersurface p hp).fromSpecResidueField P.val) default)) ∈
      (originalNormalizedHypersurfaceChartEmbedding312 r hr j).opensRange) :
    ∃ Q : FiniteFlatHilbertPoint195
        (Spec.map (CommRingCat.ofHom (R := B)
          (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
          (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
        ((hypersurfaceToBase p hp).residueDegree P.val),
      Q.val.comap (originalNormalizedProjectiveReductionOfEquation317
        (algebraMap B S) r hr s hs heBS j) =
        I0.val.comap (originalNormalizedHypersurfaceChartEmbedding312 s hs j) := by
  subst s
  simpa only [originalNormalizedProjectiveReductionOfEquation_default317] using
    (originalClosedPoint_normalizedChart_squareZeroLift317
      hBS hI r hr b hb p hp hp0 heSK P I0 u0 HZ j hx)

section OriginalCanonicalPoint
variable (R : Type u) [CommRing R] (r : MvPolynomial (Fin 4) R)
variable (hr : r.IsHomogeneous 3) (K : Type u) [Field K] [Algebra R K]
variable (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
local notation "pointDegree" => Scheme.Hom.residueDegree (hypersurfaceToBase (r.map (algebraMap R K))
  (hr.map (algebraMap R K))) P.val
local notation "pointPositive" => originalClosedPoint_residueDegree_pos317 R r hr K P

/-- INFERRED native application stage: accepted generic rank-n all-thin producer, before any point-degree substitution. No supplied fibre outcome. -/
private def originalGenericAllThinFibreFactory006
    (j : Fin 4) :=
  originalCoefficient_allThinProjectiveTestFibres317 R r hr K P j

/-- INFERRED native application stage: substitute ONLY the ORIGINAL actual point residue degree. No supplied fibre outcome. -/
private def originalActualPointDegreeFibreFactory006
    (j : Fin 4) :=
  originalGenericAllThinFibreFactory006 R r hr K P j pointDegree

/-- INFERRED native application stage: substitute ONLY its already-derived positive degree. No supplied fibre outcome. -/
private def originalActualPositiveDegreeFibreFactory006
    (j : Fin 4) :=
  originalActualPointDegreeFibreFactory006 R r hr K P j pointPositive

/-- INFERRED native application stage: substitute the SAME original coefficient chart index. No supplied fibre outcome. -/
private def originalActualCoefficientIndexFibreFactory006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree) :=
  originalActualPositiveDegreeFibreFactory006 R r hr K P j i

/-- INFERRED native application stage: substitute the SAME field-valued coefficient map. No supplied fibre outcome. -/
private def originalActualFieldMapFibreFactory006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) :=
  originalActualCoefficientIndexFibreFactory006 R r hr K P j i k

/-- INFERRED native application stage: substitute its genuine surjectivity proof. No supplied fibre outcome. -/
private def originalActualSurjectiveFieldMapFibreFactory006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k) :=
  originalActualFieldMapFibreFactory006 R r hr K P j i k hk

/-- INFERRED native application stage: substitute ORIGINAL whole field-family=P kernel; return accepted NAMED all-thin predicate. No supplied fibre outcome. -/
private def originalActualChosenAllThinFibreFactory006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker) :=
  originalActualSurjectiveFieldMapFibreFactory006 R r hr K P j i k hk hpoint

/-- INFERRED native application stage: introduce ONLY the actual presentation variable count. No supplied fibre outcome. -/
private def originalActualPresentationVariablesFibreFactory006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    (v : ℕ) :=
  originalActualChosenAllThinFibreFactory006 R r hr K P j i k hk hpoint v

/-- INFERRED native application stage: introduce ONLY the actual original-ground polynomial presentation. No supplied fibre outcome. -/
private def originalActualPresentationFibreFactory006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ}
    (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i) :=
  originalActualPresentationVariablesFibreFactory006 R r hr K P j i k hk hpoint v f

/-- INFERRED native application stage: introduce ONLY its genuine surjectivity proof. No supplied fibre outcome. -/
private def originalActualSurjectivePresentationFibreFactory006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ}
    (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) :=
  originalActualPresentationFibreFactory006 R r hr K P j i k hk hpoint f hf

/-- INFERRED native application stage: introduce actual prime q with its native IsPrime dictionary; do not expand the final fibre. No supplied fibre outcome. -/
private def originalActualPrimeIdealFibreFactory006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ}
    (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f)
    (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime] :=
  originalActualSurjectivePresentationFibreFactory006 R r hr K P j i k hk hpoint f hf q

/-- INFERRED native application stage: introduce ONLY the same field-map kernel equality. No supplied fibre outcome. -/
private def originalActualKernelPrimeFibreFactory006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ}
    (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f)
    (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) :=
  originalActualPrimeIdealFibreFactory006 R r hr K P j i k hk hpoint f hf q hq

/-- INFERRED native application stage: introduce ONLY the canonical thin test exponent. No supplied fibre outcome. -/
private def originalActualTestExponentFibreFactory006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ}
    (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f)
    (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q)
    (N : ℕ) :=
  originalActualKernelPrimeFibreFactory006 R r hr K P j i k hk hpoint f hf q hq N

/-- INFERRED native application stage: infer the final ORIGINAL thin-family u0/HZ proposition from native application, no destruct/repack or expected literal target. No supplied fibre outcome. -/
private def originalActualPositiveTestFibre006
    (j : Fin 4)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ}
    (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f)
    (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q)
    (N : ℕ) (hN : 0 < N) :=
  originalActualTestExponentFibreFactory006 R r hr K P j i k hk hpoint f hf q hq N hN

/-- OPTIONAL final typed boundary, AFTER the inferred native producer:
the actual u0/HZ result meets the EXACT original root005 target. Only unused
scalar lets differ; all actual geometric maps and ideals remain unchanged. -/
private theorem originalActualThinFibreExactTarget006
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :
    let LP := Localization.AtPrime (q.comap f.toRingHom)
    let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
    let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
    let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
    let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
    let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
    letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
    let heBS : (r.map (algebraMap R Thick)).map (algebraMap Thick Thin) =
        r.map (algebraMap R Thin) := originalNormalizedTestEquation317 R pi r
    let heSK : (r.map (algebraMap R Thin)).map b.toRingHom =
        r.map (algebraMap R K) := originalNormalizedTestEquation317 R b r
    ∃ u0 : Spec ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).residueField P.val) ⟶
        (originalThinCoefficientProjectiveFamily317
          R pointDegree r hr j pointPositive i f hf q N).val.subscheme,
      IsPullback u0
        ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val)
        (originalThinCoefficientProjectiveFamily317
          R pointDegree r hr j pointPositive i f hf q N).val.subschemeι
        (hypersurfaceReductionMap b.toRingHom
          (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin))
          (r.map (algebraMap R K)) (hr.map (algebraMap R K)) heSK) :=
  originalActualPositiveTestFibre006 R r hr K P j i k hk hpoint f hf q hq N hN

/-- SOURCE ONLY independent body boundary: Actual thick cubic smoothness, quotient reduction and specified equations. -/
private theorem originalCanonicalScalarSmoothEquationsStage317
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :
    let LP := Localization.AtPrime (q.comap f.toRingHom)
    let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
    let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
    let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
    let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
    let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
    letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
    let heBS : (r.map (algebraMap R Thick)).map (algebraMap Thick Thin) =
        r.map (algebraMap R Thin) := originalNormalizedTestEquation317 R pi r
    let heSK : (r.map (algebraMap R Thin)).map b.toRingHom =
        r.map (algebraMap R K) := originalNormalizedTestEquation317 R b r
    Smooth (hypersurfaceToBase (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))) ∧
      IsLocalRing Thin ∧ IsArtinianRing Thin ∧
      Function.Surjective (algebraMap Thick Thin) ∧
      (RingHom.ker (algebraMap Thick Thin)) ^ 2 = ⊥ ∧
      (r.map (algebraMap R Thick)).map (algebraMap Thick Thin) = r.map (algebraMap R Thin) ∧
      (r.map (algebraMap R Thin)).map b.toRingHom = r.map (algebraMap R K) ∧
      Function.Surjective b.toRingHom := by
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  have hthin := canonicalPolynomialThin_localArtinian317 f q N hN
  letI : IsLocalRing Thin := hthin.1
  letI : IsArtinianRing Thin := hthin.2
  letI : Smooth (hypersurfaceToBase (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))) :=
    smooth_hypersurfaceToBase_map (algebraMap R Thick) r hr
  have hBS : Function.Surjective (algebraMap Thick Thin) :=
    canonicalPolynomialTestPi_surjective317 f q N
  have hsq : (RingHom.ker (algebraMap Thick Thin)) ^ 2 = ⊥ :=
    canonicalPolynomialTestPi_kernel_sq_zero317 f q N
  have heBS : (r.map (algebraMap R Thick)).map (algebraMap Thick Thin) =
      r.map (algebraMap R Thin) := originalNormalizedTestEquation317 R pi r
  have heSK : (r.map (algebraMap R Thin)).map b.toRingHom =
      r.map (algebraMap R K) := originalNormalizedTestEquation317 R b r
  have hb : Function.Surjective b.toRingHom :=
    originalPresentationThinFieldMap_surjective317 f hf q k hq hk N hN
  exact ⟨inferInstance, hthin.1, hthin.2, hBS, hsq, heBS, heSK, hb⟩

/-- Actual chart membership is derived independently of the fibre witness.
Only the SAME quotient scalar structure and original equation diagrams are
used; no smooth/thin-Artinian/family construction is replayed in this cut. -/
private theorem originalCanonicalUpstairsChartMembership007
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :
    let LP := Localization.AtPrime (q.comap f.toRingHom)
    let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
    let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
    let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
    let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
    let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
    letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
    let heBS : (r.map (algebraMap R Thick)).map (algebraMap Thick Thin) =
        r.map (algebraMap R Thin) := originalNormalizedTestEquation317 R pi r
    let heSK : (r.map (algebraMap R Thin)).map b.toRingHom =
        r.map (algebraMap R K) := originalNormalizedTestEquation317 R b r
    hypersurfaceReductionMap (algebraMap Thick Thin)
      (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))
      (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) heBS
      (hypersurfaceReductionMap b.toRingHom
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin))
        (r.map (algebraMap R K)) (hr.map (algebraMap R K)) heSK
        (((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField
          P.val) default)) ∈
      (originalNormalizedHypersurfaceChartEmbedding312
        (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick)) j).opensRange := by
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  have heBS : (r.map (algebraMap R Thick)).map (algebraMap Thick Thin) =
      r.map (algebraMap R Thin) := originalNormalizedTestEquation317 R pi r
  have heSK : (r.map (algebraMap R Thin)).map b.toRingHom =
      r.map (algebraMap R K) := originalNormalizedTestEquation317 R b r
  have hS : hypersurfaceReductionMap b.toRingHom
      (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin))
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) heSK P.val ∈
      Set.range (originalNormalizedHypersurfaceChartEmbedding312
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) j) :=
    canonicalChartReduction_mem317
      (originalNormalizedProjectiveReductionOfEquation317 b.toRingHom
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin))
        (r.map (algebraMap R K)) (hr.map (algebraMap R K)) heSK j)
      (originalNormalizedHypersurfaceChartEmbedding312
        (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j)
      (originalNormalizedHypersurfaceChartEmbedding312
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) j)
      (hypersurfaceReductionMap b.toRingHom
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin))
        (r.map (algebraMap R K)) (hr.map (algebraMap R K)) heSK)
      (originalNormalizedProjectiveReductionOfEquation_toOriginal317 b.toRingHom
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin))
        (r.map (algebraMap R K)) (hr.map (algebraMap R K)) heSK j) P.val hP
  have hB := canonicalChartReduction_mem317
      (originalNormalizedProjectiveReductionOfEquation317 (algebraMap Thick Thin)
        (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) heBS j)
      (originalNormalizedHypersurfaceChartEmbedding312
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) j)
      (originalNormalizedHypersurfaceChartEmbedding312
        (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick)) j)
      (hypersurfaceReductionMap (algebraMap Thick Thin)
        (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) heBS)
      (originalNormalizedProjectiveReductionOfEquation_toOriginal317 (algebraMap Thick Thin)
        (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) heBS j) _ hS
  have hx : hypersurfaceReductionMap (algebraMap Thick Thin)
      (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))
      (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) heBS
      (hypersurfaceReductionMap b.toRingHom
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin))
        (r.map (algebraMap R K)) (hr.map (algebraMap R K)) heSK
        (((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField
          P.val) default)) ∈
      (originalNormalizedHypersurfaceChartEmbedding312
        (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick)) j).opensRange := by
    simpa only [Scheme.fromSpecResidueField_apply, Scheme.Hom.mem_opensRange, Set.mem_range] using hB
  exact hx

/-- SOURCE ONLY inferred actual specialization: the actual scalar package application, before destructuring or family calls. No desired Q premise. -/
private def originalActualScalarPackageApplication011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  originalCanonicalScalarSmoothEquationsStage317 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN

/-- SOURCE ONLY inferred actual specialization: project/destructure the actual scalar package and install its three ORIGINAL local/Artinian/smooth instances. No desired Q premise. -/
private def originalActualScalarInstances011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hscalar := originalActualScalarPackageApplication011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  letI : IsLocalRing Thin := hscalar.2.1
  letI : IsArtinianRing Thin := hscalar.2.2.1
  letI : Smooth (hypersurfaceToBase (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))) := hscalar.1
  And.intro (inferInstance : IsLocalRing Thin)
    (And.intro (inferInstance : IsArtinianRing Thin)
      (inferInstance : Smooth (hypersurfaceToBase
        (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick)))))

/-- SOURCE ONLY inferred actual specialization: the checked exact native thin-fibre producer under the actual recovered scalar instances. No desired Q premise. -/
private def originalActualFibreUnderScalarInstances011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hscalar := originalActualScalarPackageApplication011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  letI : IsLocalRing Thin := hscalar.2.1
  letI : IsArtinianRing Thin := hscalar.2.2.1
  letI : Smooth (hypersurfaceToBase (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))) := hscalar.1
  let hFibre := originalActualThinFibreExactTarget006 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  hFibre

/-- SOURCE ONLY inferred actual specialization: the passed ORIGINAL chart-membership producer under the actual recovered scalar instances. No desired Q premise. -/
private def originalActualMembershipUnderScalarInstances011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hscalar := originalActualScalarPackageApplication011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  letI : IsLocalRing Thin := hscalar.2.1
  letI : IsArtinianRing Thin := hscalar.2.2.1
  letI : Smooth (hypersurfaceToBase (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))) := hscalar.1
  let hx := originalCanonicalUpstairsChartMembership007 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  hx

/-- SOURCE ONLY inferred actual specialization: fix ONLY actual thick/thin/original-field rings, canonical Algebra and derived surjectivity/square-zero kernel. No desired Q premise. -/
private def originalActualSpecifiedLiftFixedRings011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hscalar := originalActualScalarPackageApplication011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  letI : IsLocalRing Thin := hscalar.2.1
  letI : IsArtinianRing Thin := hscalar.2.2.1
  letI : Smooth (hypersurfaceToBase (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))) := hscalar.1
  specifiedOriginalNormalizedChartLift317 (B := Thick) (S := Thin) (K := K)
    hscalar.2.2.2.1 hscalar.2.2.2.2.1

/-- SOURCE ONLY inferred actual specialization: supply original thick mapped cubic/homogeneity and its derived native Smooth instance. No desired Q premise. -/
private def originalActualSpecifiedLiftThickEquation011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hscalar := originalActualScalarPackageApplication011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  letI : IsLocalRing Thin := hscalar.2.1
  letI : IsArtinianRing Thin := hscalar.2.2.1
  letI : Smooth (hypersurfaceToBase (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))) := hscalar.1
  originalActualSpecifiedLiftFixedRings011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))

/-- SOURCE ONLY inferred actual specialization: supply ONLY the specified original thin cubic and its homogeneity. No desired Q premise. -/
private def originalActualSpecifiedLiftThinEquation011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  originalActualSpecifiedLiftThickEquation011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin))

/-- SOURCE ONLY inferred actual specialization: supply ONLY the derived exact thick-to-thin polynomial equation. No desired Q premise. -/
private def originalActualSpecifiedLiftEquationCompatibility011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hscalar := originalActualScalarPackageApplication011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  letI : IsLocalRing Thin := hscalar.2.1
  letI : IsArtinianRing Thin := hscalar.2.2.1
  letI : Smooth (hypersurfaceToBase (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))) := hscalar.1
  originalActualSpecifiedLiftThinEquation011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    hscalar.2.2.2.2.2.1

/-- SOURCE ONLY inferred actual specialization: supply ONLY the actual canonical thin-to-original-field ring map. No desired Q premise. -/
private def originalActualSpecifiedLiftFieldMap011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  originalActualSpecifiedLiftEquationCompatibility011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    b.toRingHom

/-- SOURCE ONLY inferred actual specialization: supply ONLY its derived surjectivity. No desired Q premise. -/
private def originalActualSpecifiedLiftFieldMapSurjective011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hscalar := originalActualScalarPackageApplication011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  letI : IsLocalRing Thin := hscalar.2.1
  letI : IsArtinianRing Thin := hscalar.2.2.1
  letI : Smooth (hypersurfaceToBase (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))) := hscalar.1
  originalActualSpecifiedLiftFieldMap011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    hscalar.2.2.2.2.2.2.2

/-- SOURCE ONLY inferred actual specialization: supply ONLY the original mapped field cubic and homogeneity. No desired Q premise. -/
private def originalActualSpecifiedLiftOriginalFieldEquation011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  originalActualSpecifiedLiftFieldMapSurjective011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    (r.map (algebraMap R K)) (hr.map (algebraMap R K))

/-- SOURCE ONLY inferred actual specialization: supply original field nonzero/compatibility and SAME original closed point P. No desired Q premise. -/
private def originalActualSpecifiedLiftOriginalFieldPoint011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hscalar := originalActualScalarPackageApplication011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  letI : IsLocalRing Thin := hscalar.2.1
  letI : IsArtinianRing Thin := hscalar.2.2.1
  letI : Smooth (hypersurfaceToBase (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))) := hscalar.1
  originalActualSpecifiedLiftOriginalFieldEquation011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    hK0 hscalar.2.2.2.2.2.2.1 P

/-- SOURCE ONLY inferred actual specialization: supply ONLY the actual canonical projective thin family at ORIGINAL P degree. No desired Q premise. -/
private def originalActualSpecifiedLiftOriginalThinFamily011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  originalActualSpecifiedLiftOriginalFieldPoint011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    (originalThinCoefficientProjectiveFamily317 R pointDegree r hr j pointPositive i f hf q N)

/-- SOURCE ONLY inferred actual specialization: supply the genuine native u0 from the checked original thin-fibre existence. No desired Q premise. -/
private def originalActualSpecifiedLiftNativeFibreMap011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hFibre := originalActualThinFibreExactTarget006 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  originalActualSpecifiedLiftOriginalThinFamily011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    (Classical.choose hFibre)

/-- SOURCE ONLY inferred actual specialization: supply its actual IsPullback witness, without an input diagram premise. No desired Q premise. -/
private def originalActualSpecifiedLiftNativeFibreSquare011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hFibre := originalActualThinFibreExactTarget006 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  originalActualSpecifiedLiftNativeFibreMap011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    (Classical.choose_spec hFibre)

/-- SOURCE ONLY inferred actual specialization: supply ONLY the SAME original normalized projective chart index. No desired Q premise. -/
private def originalActualSpecifiedLiftOriginalChart011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  originalActualSpecifiedLiftNativeFibreSquare011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    j

/-- SOURCE ONLY inferred actual specialization: supply derived upstairs membership; INFER the actual original Q/native whole-ideal equality. No desired Q premise. -/
private def originalActualSpecifiedNativeWholeChartQ011
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let hx := originalCanonicalUpstairsChartMembership007 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
  originalActualSpecifiedLiftOriginalChart011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    hx

/-- OPTIONAL exact final target conversion, after inferred native Q.
The original whole-chart Q/ideal header is unchanged; no supplied Q outcome. -/
theorem originalCanonicalNativeWholeChartQ317
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :
    let LP := Localization.AtPrime (q.comap f.toRingHom)
    let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
    let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
    let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
    let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
    let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
    letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
    let heBS : (r.map (algebraMap R Thick)).map (algebraMap Thick Thin) =
        r.map (algebraMap R Thin) := originalNormalizedTestEquation317 R pi r
    let heSK : (r.map (algebraMap R Thin)).map b.toRingHom =
        r.map (algebraMap R K) := originalNormalizedTestEquation317 R b r
    ∃ Q : FiniteFlatHilbertPoint195
        (Spec.map (CommRingCat.ofHom (R := Thick)
          (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R Thick)) j)
          (algebraMap Thick (OriginalNormalizedHypersurfaceAlgebra312
            (r.map (algebraMap R Thick)) j)))) pointDegree,
      Q.val.comap (originalNormalizedProjectiveReductionOfEquation317
        (algebraMap Thick Thin) (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) heBS j) =
      (originalThinCoefficientProjectiveFamily317
        R pointDegree r hr j pointPositive i f hf q N).val.comap
        (originalNormalizedHypersurfaceChartEmbedding312
          (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) j) :=
  originalActualSpecifiedNativeWholeChartQ011 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN

/-- SOURCE ONLY independent body boundary: Conditional private transport of the exact whole-chart lift equality to physical point reduction; no existence claim. -/
theorem originalCanonicalNativeWholeIdealPhysicalReduction317
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :
    let LP := Localization.AtPrime (q.comap f.toRingHom)
    let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
    let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
    let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
    let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
    let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
    letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
    let heBS : (r.map (algebraMap R Thick)).map (algebraMap Thick Thin) =
        r.map (algebraMap R Thin) := originalNormalizedTestEquation317 R pi r
    let heSK : (r.map (algebraMap R Thin)).map b.toRingHom =
        r.map (algebraMap R K) := originalNormalizedTestEquation317 R b r
    ∀ Q : FiniteFlatHilbertPoint195
        (Spec.map (CommRingCat.ofHom (R := Thick)
          (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R Thick)) j)
          (algebraMap Thick (OriginalNormalizedHypersurfaceAlgebra312
            (r.map (algebraMap R Thick)) j)))) pointDegree,
      Q.val.comap (originalNormalizedProjectiveReductionOfEquation317
        (algebraMap Thick Thin) (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) heBS j) =
      (originalThinCoefficientProjectiveFamily317
        R pointDegree r hr j pointPositive i f hf q N).val.comap
        (originalNormalizedHypersurfaceChartEmbedding312
          (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) j) →
      originalNormalizedAffinePointReduction317 R pi r hr j pointDegree Q =
        originalCoefficientTestPhysicalFamily317 R pointDegree r hr j pointPositive i
          (localPolynomialArtinianChartTest316 f hf q N) := by
  let LP := Localization.AtPrime (q.comap f.toRingHom)
  let Rel : Ideal LP := RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
  let Thick := LP ⧸ obstructionThickIdeal316 (maximalIdeal LP) Rel N
  let Thin := LP ⧸ obstructionThinIdeal316 (maximalIdeal LP) Rel N
  let pi : Thick →ₐ[R] Thin := canonicalPolynomialTestPi317 f q N
  let b : Thin →ₐ[R] K := originalPresentationThinFieldMap317 f hf q k hq hk N hN
  letI : Algebra Thick Thin := canonicalPolynomialTestPiAlgebra317 f q N
  let heBS : (r.map (algebraMap R Thick)).map (algebraMap Thick Thin) =
      r.map (algebraMap R Thin) := originalNormalizedTestEquation317 R pi r
  let heSK : (r.map (algebraMap R Thin)).map b.toRingHom =
      r.map (algebraMap R K) := originalNormalizedTestEquation317 R b r
  change ∀ Q : FiniteFlatHilbertPoint195
        (Spec.map (CommRingCat.ofHom (R := Thick)
          (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R Thick)) j)
          (algebraMap Thick (OriginalNormalizedHypersurfaceAlgebra312
            (r.map (algebraMap R Thick)) j)))) pointDegree,
      Q.val.comap (originalNormalizedProjectiveReductionOfEquation317
        (algebraMap Thick Thin) (r.map (algebraMap R Thick)) (hr.map (algebraMap R Thick))
        (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) heBS j) =
      (originalThinCoefficientProjectiveFamily317
        R pointDegree r hr j pointPositive i f hf q N).val.comap
        (originalNormalizedHypersurfaceChartEmbedding312
          (r.map (algebraMap R Thin)) (hr.map (algebraMap R Thin)) j) →
      originalNormalizedAffinePointReduction317 R pi r hr j pointDegree Q =
        originalCoefficientTestPhysicalFamily317 R pointDegree r hr j pointPositive i
          (localPolynomialArtinianChartTest316 f hf q N)
  intro Q hQ
  apply Subtype.ext
  exact (originalNormalizedAffinePointReduction_wholeIdeal317 R pi r hr j pointDegree Q).trans
    (hQ.trans (originalCoefficientTestProjectiveFamily_chartComap317
      R pointDegree r hr j pointPositive i (localPolynomialArtinianChartTest316 f hf q N)))

end OriginalCanonicalPoint
end PfaffianDescent
end

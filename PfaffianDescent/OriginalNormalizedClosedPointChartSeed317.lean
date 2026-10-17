import PfaffianDescent.NativeClosedPointHilbertSeed317
import PfaffianDescent.OriginalNormalizedAffinePointToProjective317

/-! SOURCE ONLY317. The ORIGINAL closed point supplies a normalized physical
chart seed of its actual residue degree. Its whole projective push is exactly
the original point kernel, with no comparison or residue-HZ premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Reversing a base-projection cast recovers the ORIGINAL point before
any concrete normalized quotient or projective hypersurface is supplied. -/
private theorem closedPointChartProjection_reverse317
    {Y T : Scheme.{u}} {F G : Y ⟶ T} (h : F = G) (n : ℕ)
    (Q : FiniteFlatHilbertPoint195 F n) :
    nativeFiniteFlatPointProjectionEq317 h.symm n
      (nativeFiniteFlatPointProjectionEq317 h n Q) = Q := by
  cases h
  rfl

/-- Use only membership of the ORIGINAL point in the chart and the proved
scalar projection equality to obtain the physical chart seed. -/
private def closedPointChartProjectionSeed317
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (F : X ⟶ Spec (.of K)) [LocallyOfFiniteType F] (P : closedPoints X)
    (a : Y ⟶ X) [IsOpenImmersion a] (G : Y ⟶ Spec (.of K))
    (h : a ≫ F = G) (hP : P.val ∈ Set.range a) :
    FiniteFlatHilbertPoint195 G (F.residueDegree P.val) :=
  nativeFiniteFlatPointProjectionEq317 h (F.residueDegree P.val)
    (nativeClosedPointOpenHilbertSeed317 F P a hP)

private theorem closedPointChartProjectionSeed_ideal317
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (F : X ⟶ Spec (.of K)) [LocallyOfFiniteType F] (P : closedPoints X)
    (a : Y ⟶ X) [IsOpenImmersion a] (G : Y ⟶ Spec (.of K))
    (h : a ≫ F = G) (hP : P.val ∈ Set.range a) :
    (closedPointChartProjectionSeed317 F P a G h hP).val =
      (X.fromSpecResidueField P.val).ker.comap a :=
  (nativeFiniteFlatPointProjectionEq_wholeIdeal317 h (F.residueDegree P.val)
    (nativeClosedPointOpenHilbertSeed317 F P a hP)).trans
      (nativeClosedPointOpenHilbertSeed_ideal317 F P a hP)

/-- The accepted315 push/lift inverse recovers the whole ORIGINAL point.
The whole-family membership proof is derived from the seed singleton range,
not supplied as a stronger assumption than point membership. -/
private theorem closedPointChartProjectionSeed_push317
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (F : X ⟶ Spec (.of K)) [LocallyOfFiniteType F] [IsSeparated F]
    (P : closedPoints X) (a : Y ⟶ X) [IsOpenImmersion a]
    (G : Y ⟶ Spec (.of K)) (h : a ≫ F = G) (hP : P.val ∈ Set.range a) :
    nativeFiniteFlatPointPushOpen314 a F (F.residueDegree P.val)
      (nativeFiniteFlatPointProjectionEq317 h.symm (F.residueDegree P.val)
        (closedPointChartProjectionSeed317 F P a G h hP)) =
      nativeClosedPointHilbertSeed317 F P := by
  have hrange : Set.range (nativeClosedPointHilbertSeed317 F P).val.subschemeι ⊆ Set.range a := by
    rw [nativeClosedPointHilbertSeed_range317]
    exact Set.singleton_subset_iff.mpr hP
  exact (congrArg (nativeFiniteFlatPointPushOpen314 a F (F.residueDegree P.val))
    (closedPointChartProjection_reverse317 h (F.residueDegree P.val)
      (nativeClosedPointOpenHilbertSeed317 F P a hP))).trans
        (nativeOpenContainedFiniteFlatPoint_push_lift315 a F (F.residueDegree P.val)
          (nativeClosedPointHilbertSeed317 F P) hrange)

/-- Whole ideal version of the same native push/lift identity. All dictionaries
are kept abstract here; the actual original chart caller supplies proved312
open and hypersurface proper/separated/finite-type instances explicitly. -/
private theorem closedPointChartProjectionSeed_pushIdeal317
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (F : X ⟶ Spec (.of K)) [LocallyOfFiniteType F] [IsSeparated F]
    (P : closedPoints X) (a : Y ⟶ X) [IsOpenImmersion a]
    (G : Y ⟶ Spec (.of K)) (h : a ≫ F = G) (hP : P.val ∈ Set.range a) :
    (nativeFiniteFlatPointPushOpen314 a F (F.residueDegree P.val)
      (nativeFiniteFlatPointProjectionEq317 h.symm (F.residueDegree P.val)
        (closedPointChartProjectionSeed317 F P a G h hP))).val =
      (X.fromSpecResidueField P.val).ker :=
  (congrArg Subtype.val (closedPointChartProjectionSeed_push317 F P a G h hP)).trans
    (nativeClosedPointHilbertSeed_ideal317 F P)

local instance originalNormalizedClosedPointSeedChartOpen317
    {A : Type u} [CommRing A] (p : MvPolynomial (Fin 4) A)
    {e : ℕ} (hp : p.IsHomogeneous e) (j : Fin 4) :
    IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 p hp j) :=
  originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 p hp j

variable (R : Type u) [CommRing R] (r : MvPolynomial (Fin 4) R)
variable {d : ℕ} (hr : r.IsHomogeneous d) (K : Type u) [Field K] [Algebra R K]
variable (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
variable (j : Fin 4)
variable (hP : P.val ∈
  (originalNormalizedHypersurfaceChartEmbedding312
    (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)

/-- The physical normalized seed from the ORIGINAL ground equation r and
its ORIGINAL field closed point P. Its rank is literally the original
hypersurface projection's residue degree at P, not an assumed integer. -/
def originalNormalizedClosedPointChartSeed317 :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (R := K)
        (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j)
        (algebraMap K (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j))))
      ((hypersurfaceToBase (r.map (algebraMap R K))
        (hr.map (algebraMap R K))).residueDegree P.val) :=
  @closedPointChartProjectionSeed317
    K _ (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K)))
    (Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j)))
    (hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K)))
    (@IsProper.toLocallyOfFiniteType _ _ _
      (isProper_hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
    P (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j)
    (originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j)
    (Spec.map (CommRingCat.ofHom (R := K)
      (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j)
      (algebraMap K (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j))))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j) hP

/-- EXACT whole ideal of the ORIGINAL closed point restricted to its actual
normalized chart. This derives the field seed and its kernel identity rather
than assuming either a chart family or a comparison result. -/
lemma originalNormalizedClosedPointChartSeed_wholeIdeal317 :
    (originalNormalizedClosedPointChartSeed317 R r hr K P j hP).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField
        P.val).ker.comap (originalNormalizedHypersurfaceChartEmbedding312
          (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j) :=
  @closedPointChartProjectionSeed_ideal317
    K _ (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K)))
    (Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j)))
    (hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K)))
    (@IsProper.toLocallyOfFiniteType _ _ _
      (isProper_hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
    P (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j)
    (originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j)
    (Spec.map (CommRingCat.ofHom (R := K)
      (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j)
      (algebraMap K (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j))))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j) hP

/-- Pushing the physical normalized seed through the SAME actual chart
embedding recovers the ORIGINAL closed point's whole projective kernel.
The proof uses the accepted native315 push/lift inverse; no projective
comparison or physical HZ is supplied as a new premise. -/
lemma originalNormalizedClosedPointChartSeed_pushWholeIdeal317 :
    (originalNormalizedAffinePointToProjective317
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j
      ((hypersurfaceToBase (r.map (algebraMap R K))
        (hr.map (algebraMap R K))).residueDegree P.val)
      (originalNormalizedClosedPointChartSeed317 R r hr K P j hP)).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField
        P.val).ker :=
  @closedPointChartProjectionSeed_pushIdeal317
    K _ (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K)))
    (Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j)))
    (hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K)))
    (@IsProper.toLocallyOfFiniteType _ _ _
      (isProper_hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
    (originalNormalizedWholeOpen_separated317
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)))
    P (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j)
    (originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j)
    (Spec.map (CommRingCat.ofHom (R := K)
      (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j)
      (algebraMap K (OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R K)) j))))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j) hP

end PfaffianDescent
end

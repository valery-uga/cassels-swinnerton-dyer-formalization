import PfaffianDescent.OriginalNormalizedWholeOpenPoint317

/-! SOURCE ONLY317. Whole-open point and physical whole-ideal reduction give
an existential lift on the SAME normalized original chart. This module uses
no Artinian, smoothness, closed-residue-point or physical HZ assumptions. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
local instance normalizedWholeOpenChartLiftOpen317
    {B : Type u} [CommRing B] (r : MvPolynomial (Fin 4) B)
    {d : ℕ} (hr : r.IsHomogeneous d) (j : Fin 4) :
    IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 r hr j) :=
  originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 r hr j

/-- Assemble the existential point and its WHOLE ideal reduction while all
scheme maps, Hilbert-point carrier and ideal dictionaries remain abstract.
No concrete normalized chart or transparent local point is reconstructed. -/
private theorem wholePointChartReductionExistence317
    {Y Y0 T : Scheme.{u}} (F : Y ⟶ T) (n : ℕ)
    (J : Y.IdealSheafData) (Q : FiniteFlatHilbertPoint195 F n)
    (hQ : Q.val = J) (v : Y0 ⟶ Y) (J0 : Y0.IdealSheafData)
    (hred : J.comap v = J0) :
    ∃ Q' : FiniteFlatHilbertPoint195 F n, Q'.val.comap v = J0 :=
  ⟨Q, (congrArg (fun H : Y.IdealSheafData => H.comap v) hQ).trans hred⟩

/-- The accepted ACTUAL normalized whole-open point and accepted physical
projective reduction assemble into a chart lift, for arbitrary degree/n and
arbitrary ring homomorphism. All ideals include their nilpotent structure. -/
lemma originalNormalizedWholeOpen_physicalReduction_chartLift317
    {B S : Type u} [CommRing B] [CommRing S]
    (c : B →+* S) (r : MvPolynomial (Fin 4) B)
    {d : ℕ} (hr : r.IsHomogeneous d) (j : Fin 4) (n : ℕ)
    (I : FiniteFlatHilbertPoint195 (hypersurfaceToBase r hr) n)
    (QU : FiniteFlatHilbertPoint195
      ((originalNormalizedHypersurfaceChartEmbedding312 r hr j).opensRange.ι ≫
        hypersurfaceToBase r hr) n)
    (hwhole : QU.val.map
      (originalNormalizedHypersurfaceChartEmbedding312 r hr j).opensRange.ι = I.val)
    (I0 : FiniteFlatHilbertPoint195
      (hypersurfaceToBase (r.map c) (hr.map c)) n)
    (hphysical : I.val.comap
      (hypersurfaceReductionMap c r hr (r.map c) (hr.map c) rfl) = I0.val) :
    ∃ Q : FiniteFlatHilbertPoint195
        (Spec.map (CommRingCat.ofHom (R := B)
          (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
          (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j)))) n,
      Q.val.comap (originalNormalizedProjectiveChartReduction312 c r hr j) =
        I0.val.comap (originalNormalizedHypersurfaceChartEmbedding312
          (r.map c) (hr.map c) j) :=
  @wholePointChartReductionExistence317
    (Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 r j)))
    (Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 (r.map c) j)))
    (Spec (.of B))
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j)))) n
    (I.val.comap (originalNormalizedHypersurfaceChartEmbedding312 r hr j))
    (@originalNormalizedWholeOpen_chartPoint317 B _ r d hr j n I QU hwhole)
    (@originalNormalizedWholeOpen_chartPoint_wholeIdeal317 B _ r d hr j n I QU hwhole)
    (originalNormalizedProjectiveChartReduction312 c r hr j)
    (I0.val.comap (originalNormalizedHypersurfaceChartEmbedding312
      (r.map c) (hr.map c) j))
    (@originalNormalizedProjectiveChartReduction_wholeIdeal312
      B S _ _ c r d hr j I.val I0.val hphysical)

/-- Convert a whole-open existential witness to the SAME normalized chart
existential before the original Artinian/residue provider is specialized.
The physical reduction premise is the genuine original whole ideal equality. -/
lemma originalNormalizedWholeOpenWitness_chartLift317
    {B S : Type u} [CommRing B] [CommRing S]
    (c : B →+* S) (r : MvPolynomial (Fin 4) B)
    {d : ℕ} (hr : r.IsHomogeneous d) (j : Fin 4) (n : ℕ)
    (I0 : FiniteFlatHilbertPoint195
      (hypersurfaceToBase (r.map c) (hr.map c)) n)
    (H : ∃ (QU : FiniteFlatHilbertPoint195
        ((originalNormalizedHypersurfaceChartEmbedding312 r hr j).opensRange.ι ≫
          hypersurfaceToBase r hr) n)
      (I : FiniteFlatHilbertPoint195 (hypersurfaceToBase r hr) n),
      QU.val.map (originalNormalizedHypersurfaceChartEmbedding312 r hr j).opensRange.ι = I.val ∧
      I.val.comap (hypersurfaceReductionMap c r hr (r.map c) (hr.map c) rfl) = I0.val) :
    ∃ Q : FiniteFlatHilbertPoint195
        (Spec.map (CommRingCat.ofHom (R := B)
          (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
          (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j)))) n,
      Q.val.comap (originalNormalizedProjectiveChartReduction312 c r hr j) =
        I0.val.comap (originalNormalizedHypersurfaceChartEmbedding312
          (r.map c) (hr.map c) j) := by
  obtain ⟨QU, I, hwhole, hphysical⟩ := H
  exact @originalNormalizedWholeOpen_physicalReduction_chartLift317
    B S _ _ c r d hr j n I QU hwhole I0 hphysical

end PfaffianDescent
end

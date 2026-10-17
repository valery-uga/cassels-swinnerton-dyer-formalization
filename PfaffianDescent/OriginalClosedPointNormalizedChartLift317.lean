import PfaffianDescent.OriginalNormalizedWholeOpenChartLift317
import PfaffianDescent.OriginalClosedPointWholeOpenWitness317

/-! SOURCE ONLY317. Original public header preserved from001. Heavy native
point construction is checked at GENERIC Scheme types first; the actual
original cubic provider is a separate checked cut. No limit increase. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
local instance normalizedOriginalChartOpen317
    {B : Type u} [CommRing B] (r : MvPolynomial (Fin 4) B)
    {d : ℕ} (hr : r.IsHomogeneous d) (j : Fin 4) :
    IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 r hr j) :=
  originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 r hr j

lemma originalClosedPoint_normalizedChart_squareZeroLift317
    {B S K : Type u} [CommRing B] [CommRing S] [Field K]
    [Algebra B S] [IsArtinianRing S] [IsLocalRing S]
    (hBS : Function.Surjective (algebraMap B S))
    (hI : (RingHom.ker (algebraMap B S)) ^ 2 = ⊥)
    (r : MvPolynomial (Fin 4) B) (hr : r.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase r hr)]
    (b : S →+* K) (hb : Function.Surjective b)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (he : (r.map (algebraMap B S)).map b = p)
    (P : closedPoints (hypersurface p hp))
    (I0 : FiniteFlatHilbertPoint195
      (hypersurfaceToBase (r.map (algebraMap B S)) (hr.map (algebraMap B S)))
      ((hypersurfaceToBase p hp).residueDegree P.1))
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ I0.val.subscheme)
    (HZ : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      I0.val.subschemeι
      (hypersurfaceReductionMap b (r.map (algebraMap B S)) (hr.map (algebraMap B S)) p hp he))
    (j : Fin 4)
    (hx : hypersurfaceReductionMap (algebraMap B S) r hr
        (r.map (algebraMap B S)) (hr.map (algebraMap B S)) rfl
      (hypersurfaceReductionMap b (r.map (algebraMap B S)) (hr.map (algebraMap B S)) p hp he
        (((hypersurface p hp).fromSpecResidueField P.1) default)) ∈
      (originalNormalizedHypersurfaceChartEmbedding312 r hr j).opensRange) :
    ∃ Q : FiniteFlatHilbertPoint195
        (Spec.map (CommRingCat.ofHom (R := B)
          (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
          (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
        ((hypersurfaceToBase p hp).residueDegree P.1),
      Q.val.comap (originalNormalizedProjectiveChartReduction312 (algebraMap B S) r hr j) =
        I0.val.comap (originalNormalizedHypersurfaceChartEmbedding312
          (r.map (algebraMap B S)) (hr.map (algebraMap B S)) j) := by
  exact @originalNormalizedWholeOpenWitness_chartLift317
    B S _ _ (algebraMap B S) r 3 hr j
    ((hypersurfaceToBase p hp).residueDegree P.1) I0
    (originalClosedPoint_wholeOpenWitness317 hBS hI r hr b hb p hp hp0 he P I0 u0 HZ j hx)

end PfaffianDescent
end

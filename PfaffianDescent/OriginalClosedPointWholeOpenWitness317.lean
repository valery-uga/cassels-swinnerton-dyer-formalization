import PfaffianDescent.OriginalCubicFixedOpenSquareZeroHilbertLift312
import PfaffianDescent.OriginalNormalizedProjectiveReduction312

/-! SOURCE ONLY317. One bounded call to accepted original312,
returning the original whole open point and a PHYSICAL ideal reduction.
No normalized quotient point construction occurs in this declaration. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
local instance normalizedOriginalWitnessChartOpen317
    {B : Type u} [CommRing B] (r : MvPolynomial (Fin 4) B)
    {d : ℕ} (hr : r.IsHomogeneous d) (j : Fin 4) :
    IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 r hr j) :=
  originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 r hr j

lemma originalClosedPoint_wholeOpenWitness317
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
    let F := hypersurfaceToBase r hr
    let n := (hypersurfaceToBase p hp).residueDegree P.1
    let a := originalNormalizedHypersurfaceChartEmbedding312 r hr j
    let U := a.opensRange
    let d := hypersurfaceReductionMap (algebraMap B S) r hr
      (r.map (algebraMap B S)) (hr.map (algebraMap B S)) rfl
    ∃ (QU : FiniteFlatHilbertPoint195 (U.ι ≫ F) n) (I' : FiniteFlatHilbertPoint195 F n),
      QU.val.map U.ι = I'.val ∧ I'.val.comap d = I0.val := by
  let F := hypersurfaceToBase r hr
  let F0 := hypersurfaceToBase (r.map (algebraMap B S)) (hr.map (algebraMap B S))
  let n := (hypersurfaceToBase p hp).residueDegree P.1
  let a := originalNormalizedHypersurfaceChartEmbedding312 r hr j
  let U := a.opensRange
  let d := hypersurfaceReductionMap (algebraMap B S) r hr
    (r.map (algebraMap B S)) (hr.map (algebraMap B S)) rfl
  obtain ⟨QU, I', hwhole, hred⟩ :=
    originalClosedPoint_anyNeighborhood_squareZeroHilbertTests_surjective312
      hBS hI r hr (r.map (algebraMap B S)) (hr.map (algebraMap B S)) rfl
      b hb p hp hp0 he P I0 u0 HZ U hx
  have hphysical : I'.val.comap d = I0.val :=
    congrArg (fun J : FiniteFlatHilbertPoint195 F0 n => J.val) hred
  exact ⟨QU, I', hwhole, hphysical⟩

end PfaffianDescent
end

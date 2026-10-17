import PfaffianDescent.FiniteFlatHilbertNoetherianDatum279
import PfaffianDescent.OriginalCubicSquareZeroHilbertTests195

/-! Source only279. Actual195 whole-ideal Artin lifts become genuine
FiniteSubschemeDatum lifts: native LFP is derived from a Noetherian upstairs
base, including every Artin test. No representability/smoothness premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma originalClosedPoint_squareZeroFiniteSubschemeDatum_surjective279
    {R S K : Type u} [CommRing R] [IsNoetherianRing R] [CommRing S] [Field K]
    [Algebra R S] [IsArtinianRing S] [IsLocalRing S]
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (r : MvPolynomial (Fin 4) R) (hr : r.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase r hr)]
    (s : MvPolynomial (Fin 4) S) (hs : s.IsHomogeneous 3)
    (heRS : r.map (algebraMap R S) = s)
    (b : S →+* K) (hb : Function.Surjective b)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (heSK : s.map b = p) (P : closedPoints (hypersurface p hp))
    (I0 : AllCharacteristics.FiniteSubschemeDatum (hypersurfaceToBase s hs)
      ((hypersurfaceToBase p hp).residueDegree P.1))
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ I0.val.subscheme)
    (HZ : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      I0.val.subschemeι (hypersurfaceReductionMap b s hs p hp heSK)) :
    let F := hypersurfaceToBase r hr
    let F0 := hypersurfaceToBase s hs
    let d := hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
    let beta := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let n := (hypersurfaceToBase p hp).residueDegree P.1
    let H := isPullback_hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
    ∃ I' : AllCharacteristics.FiniteSubschemeDatum F n,
      AllCharacteristics.FiniteSubschemeDatum.baseChange d beta H I' = I0 := by
  dsimp only
  let I0test := finiteSubschemeDatumToHilbertPoint279
    (hypersurfaceToBase s hs) ((hypersurfaceToBase p hp).residueDegree P.1) I0
  obtain ⟨I', hI'⟩ := originalClosedPoint_squareZeroHilbertTests_surjective195
    hRS hI r hr s hs heRS b hb p hp hp0 heSK P I0test u0 HZ
  let D' := finiteFlatHilbertPointToDatum279 (hypersurfaceToBase r hr)
    ((hypersurfaceToBase p hp).residueDegree P.1) I'
  refine ⟨D', Subtype.ext ?_⟩
  change I'.val.comap (hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS) = I0.val
  exact congrArg Subtype.val hI'

lemma originalClosedPoint_artin_squareZeroFiniteSubschemeDatum_surjective279
    {R S K : Type u} [CommRing R] [IsArtinianRing R] [CommRing S] [Field K]
    [Algebra R S] [IsArtinianRing S] [IsLocalRing S]
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (r : MvPolynomial (Fin 4) R) (hr : r.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase r hr)]
    (s : MvPolynomial (Fin 4) S) (hs : s.IsHomogeneous 3)
    (heRS : r.map (algebraMap R S) = s)
    (b : S →+* K) (hb : Function.Surjective b)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (heSK : s.map b = p) (P : closedPoints (hypersurface p hp))
    (I0 : AllCharacteristics.FiniteSubschemeDatum (hypersurfaceToBase s hs)
      ((hypersurfaceToBase p hp).residueDegree P.1))
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ I0.val.subscheme)
    (HZ : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      I0.val.subschemeι (hypersurfaceReductionMap b s hs p hp heSK)) :
    let F := hypersurfaceToBase r hr
    let F0 := hypersurfaceToBase s hs
    let d := hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
    let beta := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let n := (hypersurfaceToBase p hp).residueDegree P.1
    let H := isPullback_hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
    ∃ I' : AllCharacteristics.FiniteSubschemeDatum F n,
      AllCharacteristics.FiniteSubschemeDatum.baseChange d beta H I' = I0 := by
  exact originalClosedPoint_squareZeroFiniteSubschemeDatum_surjective279
    hRS hI r hr s hs heRS b hb p hp hp0 heSK P I0 u0 HZ

end PfaffianDescent

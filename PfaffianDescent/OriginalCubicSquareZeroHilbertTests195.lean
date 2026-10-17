import PfaffianDescent.FiniteFlatHilbertTestPoints195
import PfaffianDescent.OriginalCubicSameWholeGlobalDegree191

/-! SOURCE ONLY195. Square-zero local Artin tests at an ORIGINAL closed point.
The actual lift is CONSTRUCTED by191; lift existence, ideal equality, regularity,
flatness of the desired lift, and Hilbert representability are not premises.
All Field K: no perfectness or characteristic-zero restriction. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct nonZeroDivisors
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma exists_originalCubic_squareZeroHilbertTestLift195
    {R S K : Type u} [CommRing R] [CommRing S] [Field K]
    [Algebra R S] [IsArtinianRing S] [IsLocalRing S] {Z : Scheme.{u}}
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    (r : MvPolynomial (Fin 4) R) (hr : r.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase r hr)]
    (s : MvPolynomial (Fin 4) S) (hs : s.IsHomogeneous 3)
    (heRS : r.map (algebraMap R S) = s)
    (b : S →+* K) (hb : Function.Surjective b)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (heSK : s.map b = p) (P : closedPoints (hypersurface p hp))
    (i : Z ⟶ hypersurface s hs) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase s hs)] [Flat (i ≫ hypersurfaceToBase s hs)]
    (u0 : Spec ((hypersurface p hp).residueField P.1) ⟶ Z)
    (HZ : IsPullback u0 ((hypersurface p hp).fromSpecResidueField P.1)
      i (hypersurfaceReductionMap b s hs p hp heSK)) :
    let F := hypersurfaceToBase r hr
    let F0 := hypersurfaceToBase s hs
    let d := hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
    let beta := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let n := (hypersurfaceToBase p hp).residueDegree P.1
    let H := isPullback_hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
    ∃ (Z' : Scheme.{u}) (i' : Z' ⟶ hypersurface r hr) (r0 : Z ⟶ Z'),
      IsClosedImmersion i' ∧ IsFinite (i' ≫ F) ∧ Flat (i' ≫ F) ∧
      (∀ y, (i' ≫ F).finrank y = n) ∧
      r0 ≫ i' = i ≫ d ∧ IsPullback r0 i i' d ∧
      IsPullback r0 (i ≫ F0) (i' ≫ F) beta ∧
      ∃ I' : FiniteFlatHilbertPoint195 F n,
        I'.val = i'.ker ∧
        (finiteFlatHilbertBaseChange195 d F0 F beta H n I').val = i.ker := by
  let F := hypersurfaceToBase r hr
  let F0 := hypersurfaceToBase s hs
  let d := hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
  let beta := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let n := (hypersurfaceToBase p hp).residueDegree P.1
  let H := isPullback_hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
  obtain ⟨Uup, hxU, hChart⟩ :=
    exists_originalCubic_sameWholeGlobalDegreeLift191
      hRS hI r hr s hs heRS b hb p hp hp0 heSK P i u0 HZ
  let A := Γ(hypersurface r hr, Uup)
  letI : Algebra R A := (familySpecChartRingMap171 F Uup).toAlgebra
  let a := Uup.2.fromSpec
  obtain ⟨a0, ha0, ha, hd, hs0, hPrincipal⟩ := hChart
  letI := ha0
  let U := actualAffineChartOpen181 a0
  obtain ⟨f, t, e, sigma, p0, q0, j, hj,
      heS, heSigma, hSigma, hfac, hdP, hsP, HP, hOld⟩ := hPrincipal
  letI := hj
  let T := S ⊗[R] Localization.Away t
  let J := closedAffineCoordinateIdeal180 j
  obtain ⟨hJ, hpair, hcoef, hscalar, hQfac, hQbase,
      p', q', hmap, hp', hq', hNew⟩ := hOld
  let J' := Ideal.span ({p', q'} : Set (Localization.Away t))
  let rho := prescribedQuotientReduction174
    (affineTensorFiberReduction174 (R := R) (S := S)) J' J hmap
  let i' := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫
    upstairsPrincipalChart184 (A := A) a t
  let r0 := (closedAffineQuotientIso180 j).hom ≫
    Spec.map (CommRingCat.ofHom rho.toRingHom)
  obtain ⟨hclosed, hglobal, hnewbase, hfinite, hflat, hfree,
      hnewrank, hrfac, Hambient, Hbase, hField, hResidue, hGeometric⟩ := hNew
  have hglobal' : IsClosedImmersion i' := hglobal
  have hnewbase' : i' ≫ F =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Localization.Away t) ⧸ J'))) :=
    hnewbase
  have hGeometric' : ∀ y : Spec (.of R), (i' ≫ F).finrank y = n := hGeometric
  letI := hglobal'
  have hfinite' : IsFinite (i' ≫ F) := by rw [hnewbase']; exact hfinite
  have hflat' : Flat (i' ≫ F) := by rw [hnewbase']; exact hflat
  letI := hfinite'
  letI := hflat'
  let I' := closedImmersionHilbertPoint195 F i' n hGeometric'
  have hI' : (finiteFlatHilbertBaseChange195 d F0 F beta H n I').val = i.ker :=
    finiteFlatHilbertBaseChange195_closedImmersion_ideal d F0 F beta H n
      r0 i i' hGeometric' Hambient
  refine ⟨Spec (.of ((Localization.Away t) ⧸ J')), i', r0,
    hglobal', hfinite', hflat', hGeometric', hrfac, Hambient, ?_, I', rfl, hI'⟩
  change IsPullback r0 (i ≫ F0) (i' ≫ F) beta
  rw [hnewbase']
  exact Hbase

/-- Surjectivity of the literal finite-flat Hilbert test-point map at P,
for EVERY square-zero local Artin reduction in the original family.
The target point is arbitrary; its entire ideal, not its support, is lifted. -/
lemma originalClosedPoint_squareZeroHilbertTests_surjective195
    {R S K : Type u} [CommRing R] [CommRing S] [Field K]
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
    (I0 : FiniteFlatHilbertPoint195 (hypersurfaceToBase s hs)
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
    ∃ I' : FiniteFlatHilbertPoint195 F n,
      finiteFlatHilbertBaseChange195 d F0 F beta H n I' = I0 := by
  letI : IsFinite (I0.val.subschemeι ≫ hypersurfaceToBase s hs) := I0.property.1
  letI : Flat (I0.val.subschemeι ≫ hypersurfaceToBase s hs) := I0.property.2.1
  obtain ⟨Z', i', r0, hclosed, hfinite, hflat, hrank, hcomm,
      Hambient, Hbase, I', hI', hred⟩ :=
    exists_originalCubic_squareZeroHilbertTestLift195
      hRS hI r hr s hs heRS b hb p hp hp0 heSK P I0.val.subschemeι u0 HZ
  refine ⟨I', Subtype.ext ?_⟩
  exact hred.trans I0.val.ker_subschemeι

end PfaffianDescent

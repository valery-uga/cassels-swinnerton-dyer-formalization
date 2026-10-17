import PfaffianDescent.NativeNilpotentReductionFixedOpen312
import PfaffianDescent.OriginalCubicSquareZeroHilbertTests195
import PfaffianDescent.SmoothCubicOriginalFamilyStalkBridge172

/-! SOURCE ONLY312. The original cubic square-zero deformation is constructed
by195 and then kept in ANY specified original upstairs open containing the
ENTIRE old embedded family. No new lift, regularity, flatness, chart factor,
representation or formal-smoothness conclusion is supplied as an intake. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A native point in the fixed original open, together with its original
ambient point, exact whole ideal and literal original square-zero reduction.
The open need not be affine; an affine choice gives the needed fixed-chart
input for transporting the lift to a coefficient classifier. -/
lemma originalClosedPoint_fixedOpen_squareZeroHilbertTests_surjective312
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
      I0.val.subschemeι (hypersurfaceReductionMap b s hs p hp heSK))
    (U : (hypersurface r hr).Opens)
    (hU : ∀ z : I0.val.subscheme,
      (I0.val.subschemeι ≫
        hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS) z ∈ U) :
    let F := hypersurfaceToBase r hr
    let F0 := hypersurfaceToBase s hs
    let d := hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
    let beta := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let n := (hypersurfaceToBase p hp).residueDegree P.1
    let H := isPullback_hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
    ∃ (Q : FiniteFlatHilbertPoint195 (U.ι ≫ F) n)
      (I' : FiniteFlatHilbertPoint195 F n),
      Q.val.map U.ι = I'.val ∧
      finiteFlatHilbertBaseChange195 d F0 F beta H n I' = I0 := by
  let F := hypersurfaceToBase r hr
  let F0 := hypersurfaceToBase s hs
  let d := hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
  let beta := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let n := (hypersurfaceToBase p hp).residueDegree P.1
  let H := isPullback_hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
  letI : IsFinite (I0.val.subschemeι ≫ F0) := I0.property.1
  letI : Flat (I0.val.subschemeι ≫ F0) := I0.property.2.1
  obtain ⟨Z', i', r0, hclosed, hfinite, hflat, hrank,
      hcomm, Hambient, Hbase, I', hI', hred⟩ :=
    exists_originalCubic_squareZeroHilbertTestLift195
      hRS hI r hr s hs heRS b hb p hp hp0 heSK P I0.val.subschemeι u0 HZ
  letI : IsClosedImmersion i' := hclosed
  obtain ⟨a, ha, haclosed⟩ := exists_fixedOpen_factor_of_nilpotentReduction312
    (algebraMap R S) hRS ⟨2, hI⟩ F F0 d i' I0.val.subschemeι r0 Hbase hcomm U hU
  letI : IsClosedImmersion a := haclosed
  have hbase : a ≫ (U.ι ≫ F) = i' ≫ F :=
    (Category.assoc a U.ι F).symm.trans (congrArg (fun f => f ≫ F) ha)
  letI : IsFinite (a ≫ (U.ι ≫ F)) := hbase.symm ▸ hfinite
  letI : Flat (a ≫ (U.ι ≫ F)) := hbase.symm ▸ hflat
  let Q := closedImmersionHilbertPoint195 (U.ι ≫ F) a n
    (fun y => hbase.symm ▸ hrank y)
  have hwhole : Q.val.map U.ι = I'.val :=
    (Scheme.IdealSheafData.map_ker a U.ι).trans
      ((congrArg (fun f : Z' ⟶ hypersurface r hr => f.ker) ha).trans hI'.symm)
  have hexact : finiteFlatHilbertBaseChange195 d F0 F beta H n I' = I0 :=
    Subtype.ext (hred.trans I0.val.ker_subschemeι)
  exact ⟨Q, I', hwhole, hexact⟩

/-- The only open intake is that it contains the ORIGINAL special closed
point. Entire downstairs containment and entire upstairs fixed-open lifting
are both derived; no deformation support or new chart factor is assumed. -/
lemma originalClosedPoint_anyNeighborhood_squareZeroHilbertTests_surjective312
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
      I0.val.subschemeι (hypersurfaceReductionMap b s hs p hp heSK))
    (U : (hypersurface r hr).Opens)
    (hx : hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
      (hypersurfaceReductionMap b s hs p hp heSK
        (((hypersurface p hp).fromSpecResidueField P.1) default)) ∈ U) :
    let F := hypersurfaceToBase r hr
    let F0 := hypersurfaceToBase s hs
    let d := hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
    let beta := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let n := (hypersurfaceToBase p hp).residueDegree P.1
    let H := isPullback_hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
    ∃ (Q : FiniteFlatHilbertPoint195 (U.ι ≫ F) n)
      (I' : FiniteFlatHilbertPoint195 F n),
      Q.val.map U.ι = I'.val ∧
      finiteFlatHilbertBaseChange195 d F0 F beta H n I' = I0 := by
  have hsupp := nilpotentCartesianFieldPoint_support176
    (hypersurfaceToBase s hs) b hb
    (smoothCubic_artin_residueKernel_isNilpotent172 b hb)
    (hypersurfaceReductionMap b s hs p hp heSK) (hypersurfaceToBase p hp)
    (isPullback_hypersurfaceReductionMap b s hs p hp heSK)
    I0.val.subschemeι u0 ((hypersurface p hp).fromSpecResidueField P.1) HZ
  have hU : ∀ z : I0.val.subscheme,
      (I0.val.subschemeι ≫
        hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS) z ∈ U := by
    intro z
    change hypersurfaceReductionMap (algebraMap R S) r hr s hs heRS
      (I0.val.subschemeι z) ∈ U
    rw [hsupp z]
    exact hx
  exact originalClosedPoint_fixedOpen_squareZeroHilbertTests_surjective312
    hRS hI r hr s hs heRS b hb p hp hp0 heSK P I0 u0 HZ U hU

end PfaffianDescent
end

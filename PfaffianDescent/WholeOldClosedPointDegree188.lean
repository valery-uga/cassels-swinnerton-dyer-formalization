import PfaffianDescent.FiniteFlatCartesianPointRank188
import PfaffianDescent.WholeClosedAffineQuotient180
import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.HypersurfaceReduction

/-! SOURCE ONLY / UNVERIFIED188. The SAME entire old Z, its canonical
whole coordinate quotient and its actual closed-point fiber give the
original degree under the original scalar actions. No rank or fiber-algebra
isomorphism conclusion is supplied as a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical quotient of the SAME old Z has the degree of its
specified actual Cartesian field-point fiber. -/
lemma closedAffineQuotientCartesianPoint_finrank188
    {S T K L : Type u} [CommRing S] [IsLocalRing S] [CommRing T]
    [Algebra S T] [Field K] [Field L] [Algebra K L] {Z : Scheme.{u}}
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j]
    [IsFinite (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))]
    [Flat (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))]
    (b : S →+* K) (u0 : Spec (.of L) ⟶ Z)
    (H : IsPullback u0 (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
      (Spec.map (CommRingCat.ofHom b))) :
    Module.finrank S (T ⧸ closedAffineCoordinateIdeal180 j) = Module.finrank K L := by
  obtain ⟨hbase, hfinite, hflat⟩ := closedAffineQuotient180_finite_flat (S := S) j
  letI := hfinite
  letI := hflat
  let x : PrimeSpectrum S :=
    (Spec.map (CommRingCat.ofHom b)) (IsLocalRing.closedPoint K)
  have hquot := localFiniteFlatSpec_finrank188
    (S := S) (Q := T ⧸ closedAffineCoordinateIdeal180 j) x
  have hiso := congrFun
    (Scheme.Hom.finrank_comp_left_of_isIso (closedAffineQuotientIso180 j).hom
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (T ⧸ closedAffineCoordinateIdeal180 j))))) x
  rw [hbase] at hiso
  exact hquot.symm.trans (hiso.symm.trans
    (finiteFlatCartesianFieldPoint_finrank188
      (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) b u0 H))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Paste the two ORIGINAL geometric fiber squares. The actual closed
point supplies its canonical pointAlgebra; the selected old quotient
embedding need only retain its ordinary original coefficient-map equality. -/
lemma wholeOldClosedPointQuotient_finrank188
    {S T K : Type u} [CommRing S] [IsLocalRing S] [CommRing T] [Algebra S T]
    [Field K] {X Xk Z : Scheme.{u}}
    (F : X ⟶ Spec (.of S)) (b : S →+* K)
    (d : Xk ⟶ X) (Fk : Xk ⟶ Spec (.of K))
    (H0 : IsPullback d Fk F (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) [IsFinite (i ≫ F)] [Flat (i ≫ F)]
    (P : closedPoints Xk) (u0 : Spec (Xk.residueField P.1) ⟶ Z)
    (HZ : IsPullback u0 (Xk.fromSpecResidueField P.1) i d)
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j]
    (hbase : j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) = i ≫ F) :
    letI := AllCharacteristics.pointAlgebra Fk P.1
    Module.finrank S (T ⧸ closedAffineCoordinateIdeal180 j) =
      Module.finrank K (Xk.residueField P.1) := by
  letI := AllCharacteristics.pointAlgebra Fk P.1
  letI : IsFinite (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    rw [hbase]
    infer_instance
  letI : Flat (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    rw [hbase]
    infer_instance
  have hpointBase :
      Spec.map (CommRingCat.ofHom (algebraMap K (Xk.residueField P.1))) =
        Xk.fromSpecResidueField P.1 ≫ Fk :=
    AllCharacteristics.pointAlgebra_spec Fk P.1
  have Hbase : IsPullback u0
      (Spec.map (CommRingCat.ofHom (algebraMap K (Xk.residueField P.1))))
      (j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
      (Spec.map (CommRingCat.ofHom b)) :=
    hpointBase.symm ▸ hbase.symm ▸ (HZ.paste_vert H0)
  exact closedAffineQuotientCartesianPoint_finrank188 j b u0 Hbase

/-- Literal original cubic family and original closed point. The actual
hypersurface coefficient-fiber square is constructed internally from the
original equation reduction. No smoothness/perfection restriction is needed
for this stronger finite-flat rank identification. -/
lemma originalCubicClosedPointQuotient_finrank188
    {S T K : Type u} [CommRing S] [IsLocalRing S] [CommRing T] [Algebra S T]
    [Field K] {Z : Scheme.{u}}
    (b : S →+* K) (q : MvPolynomial (Fin 4) S) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (he : q.map b = p)
    (i : Z ⟶ AllCharacteristics.HomogeneousProjective.hypersurface q hq)
    [IsFinite (i ≫ AllCharacteristics.HomogeneousProjective.hypersurfaceToBase q hq)]
    [Flat (i ≫ AllCharacteristics.HomogeneousProjective.hypersurfaceToBase q hq)]
    (P : closedPoints (AllCharacteristics.HomogeneousProjective.hypersurface p hp))
    (u0 : Spec ((AllCharacteristics.HomogeneousProjective.hypersurface p hp).residueField P.1) ⟶ Z)
    (HZ : IsPullback u0
      ((AllCharacteristics.HomogeneousProjective.hypersurface p hp).fromSpecResidueField P.1)
      i (AllCharacteristics.HomogeneousProjective.hypersurfaceReductionMap b q hq p hp he))
    (j : Z ⟶ Spec (.of T)) [IsClosedImmersion j]
    (hbase : j ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) =
      i ≫ AllCharacteristics.HomogeneousProjective.hypersurfaceToBase q hq) :
    letI := AllCharacteristics.pointAlgebra
      (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp) P.1
    Module.finrank S (T ⧸ closedAffineCoordinateIdeal180 j) =
      Module.finrank K
        ((AllCharacteristics.HomogeneousProjective.hypersurface p hp).residueField P.1) :=
  wholeOldClosedPointQuotient_finrank188
    (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase q hq) b
    (AllCharacteristics.HomogeneousProjective.hypersurfaceReductionMap b q hq p hp he)
    (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase p hp)
    (AllCharacteristics.HomogeneousProjective.isPullback_hypersurfaceReductionMap b q hq p hp he)
    i P u0 HZ j hbase

end PfaffianDescent

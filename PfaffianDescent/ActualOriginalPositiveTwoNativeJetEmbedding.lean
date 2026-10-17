import PfaffianDescent.ActualOriginalPositiveTwoPhiDualJetKernel
import PfaffianDescent.ActualNativeChartNormalizedAlgebraPoint
import PfaffianDescent.ActualKaehlerLineDualSurjectivity
import PfaffianDescent.ActualChartDualQuotientOriginalEmbedding

/- SOURCE ONLY / UNVERIFIED. Exact SAME native chart and original residue
are used both for Phi and for the dual jet. All closedness, finite rank and
reduction facts are internally derived for arbitrary surjective quotients. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ActualOriginalPositiveTwoFiber
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :=
  (moduleSpecΓFunctor (R := .of ((hypersurface p hp).residueField P.1))).obj
    ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
      (actualCubicPositiveTwoDifferentials p hp))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def actualOriginalPositiveTwoNativeJetEmbedding
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) :
    Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))) ⟶ hypersurface p hp := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  let L := (hypersurface p hp).residueField P.1
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
  exact Spec.map (CommRingCat.ofHom
    (actualKaehlerLineDualAlgebraMap (ell.comp E.symm.toLinearMap)).toRingHom) ≫
      chartι (equationIdeal p hp) C.index

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoNativeJetEmbedding_reduction
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K
      ((hypersurface p hp).residueField P.1) ((hypersurface p hp).residueField P.1)).toRingHom) ≫
        actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell =
          (hypersurface p hp).fromSpecResidueField P.1 := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  letI aK : Algebra K (ChartRing (equationIdeal p hp) C.index) :=
    (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K (ChartRing (equationIdeal p hp) C.index) := aK.toSMul
  letI : Algebra (ChartRing (equationIdeal p hp) C.index)
      ((hypersurface p hp).residueField P.1) := C.residue.toAlgebra
  letI : IsScalarTower K (ChartRing (equationIdeal p hp) C.index)
      ((hypersurface p hp).residueField P.1) := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
    ((hypersurface p hp).fromSpecResidueField P.1) C.index C.residue C.factorization
  have hred : (TrivSqZeroExt.fstHom K _ _).toRingHom.comp
      (actualKaehlerLineDualAlgebraMap (ell.comp E.symm.toLinearMap)).toRingHom = C.residue := by
    ext r
    exact actualKaehlerLineDualAlgebraMap_fst _ r
  change Spec.map _ ≫ (Spec.map _ ≫ chartι _ _) = _
  rw [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((TrivSqZeroExt.fstHom K _ _).toRingHom.comp
      (actualKaehlerLineDualAlgebraMap (ell.comp E.symm.toLinearMap)).toRingHom)) ≫ _ = _
  rw [hred]
  exact C.factorization

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    let d := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    IsClosedImmersion d ∧ ∃ hf : IsFinite (d ≫ hypersurfaceToBase p hp),
      Set.range d = {P.1} ∧
        @AllCharacteristics.finiteSchemeRank K _ _ (d ≫ hypersurfaceToBase p hp) hf = 8 := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let R := ChartRing (equationIdeal p hp) C.index
  let L := (hypersurface p hp).residueField P.1
  let qP := (hypersurface p hp).fromSpecResidueField P.1
  letI aK : Algebra K R := (chartBaseMap (equationIdeal p hp) C.index).toAlgebra
  letI : SMul K R := aK.toSMul
  letI : Algebra R L := C.residue.toAlgebra
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq
    (fun c => (RingHom.congr_fun C.base c).symm)
  let E := actualCubicPositiveTwoOriginalNativePointFiberEquiv p hp
    qP C.index C.residue C.factorization
  let phi := actualKaehlerLineDualAlgebraMap (ell.comp E.symm.toLinearMap)
  have hphi : Function.Surjective phi := actualKaehlerLineDualAlgebraMap_surjective
    C.residue_surjective _ (hell.comp E.symm.surjective)
  have hred : (TrivSqZeroExt.fstHom K L L).toRingHom.comp phi.toRingHom = C.residue := by
    ext r
    exact actualKaehlerLineDualAlgebraMap_fst _ r
  have h4 : finrank K L = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) P).trans hP
  obtain ⟨d, hd, hClosed, hbase, hreduce, hrange, hf, hRank, hSplit⟩ :=
    actualChart_dualQuotient_original_embedding (K := K) (L := L)
      (equationIdeal p hp) qP C.index
      C.residue C.base C.factorization h4 phi hphi hred
  subst d
  have hRangeP : Set.range qP = {P.1} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact Set.mem_singleton_iff.mpr ((hypersurface p hp).fromSpecResidueField_apply P.1 z)
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨IsLocalRing.closedPoint L, (hypersurface p hp).fromSpecResidueField_apply P.1 _⟩
  exact ⟨hClosed, hf, hrange.trans hRangeP, hRank⟩

end PfaffianDescent

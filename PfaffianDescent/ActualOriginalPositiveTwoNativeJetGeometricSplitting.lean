import PfaffianDescent.ActualOriginalPositiveTwoNativeJetEmbedding

/- SOURCE ONLY / UNVERIFIED. Retain the discarded geometric splitting
for the SAME original native jet, for EVERY surjective Omega(2) quotient.
The actual algebraic-closure pullback is a coproduct of FOUR length-two
dual-number schemes. No splitting/degree/rank comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualOriginalPositiveTwoNativeJetEmbedding_geometric_split
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    (ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1) (hell : Function.Surjective ell) :
    ∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
      Nonempty (pullback
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
        (actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell ≫ hypersurfaceToBase p hp) ≅
        ∐ fun _ : J => Spec (.of (DualNumber (AlgebraicClosure K)))) := by
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
  exact hSplit

end PfaffianDescent

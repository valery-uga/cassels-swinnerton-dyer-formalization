import PfaffianDescent.ActualOriginalCanonicalTensorNegativeTwoNativeJet
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetHZeroKernel
import PfaffianDescent.IntrinsicQuadraticIdealPiece

/-! SOURCE ONLY / UNVERIFIED. The literal canonical tensor-negative-two
quotient gives the SAME actual ambient ideal, including nilpotents, and
its quadratic vanishing test is q of the SAME native conormal coefficient.
Global/native Phi identification remains a separate dependency. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K : Type u} [Field K] [PerfectField K]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  (P : closedPoints (hypersurface p hp))
  (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
local notation "κ" => CommRingCat.carrier (Scheme.residueField (hypersurface p hp) (Subtype.val P))
local notation "rP" => Scheme.fromSpecResidueField (hypersurface p hp) (Subtype.val P)
local notation "E" => ModuleCat.carrier (ActualOriginalPositiveTwoFiber p hp P)
local notation "U" => actualCubicPositiveTwoDifferentialPointFiberEquiv (K := K) (L := κ) p hp rP

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma canonicalNegativeTwoArbitraryTarget_quadratic_mem_iff
    {N : Type u} [AddCommGroup N] [Module κ N]
    (hN : Module.finrank κ N = 1) (q : E →ₗ[κ] N)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    letI : IsClosedImmersion rP := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (p3ActualIdealQuadraticIntrinsicLinearEquiv
      (rP ≫ quotientProjMap (equationIdeal p hp)) s).val ∈
      intrinsicFullQuadraticSystem
        (actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hN q ≫
          quotientProjMap (equationIdeal p hp)) ↔
      q (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) = 0 := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI : IsClosedImmersion rP := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let eN : N ≃ₗ[κ] κ := oneDimensionalTargetEquivField κ N hN
  have hnative := actualOriginalPositiveTwoNativeJet_quadratic_mem_iff p hp P hP
    (normalizeOneDimensionalQuotient hN q) s
  have hzero : normalizeOneDimensionalQuotient hN q
      (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) = 0 ↔
      q (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) = 0 := by
    change eN (q (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s)) = 0 ↔
      q (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) = 0
    constructor
    · intro hz
      exact eN.injective (hz.trans eN.map_zero.symm)
    · intro hz
      exact (congrArg eN hz).trans eN.map_zero
  exact hnative.trans hzero

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equality of the actual ambient scheme-theoretic ideals, with all
nilpotents retained and original q tensor negative-two source unchanged. -/
theorem actualOriginalCanonicalTensorNegativeTwoJet_ambientIdeal_eq
    {N : Type u} [AddCommGroup N] [Module κ N]
    (hN : Module.finrank κ N = 1) (q : E →ₗ[κ] N) (hq : Function.Surjective q) :
    let qT := (actualOriginalCanonicalTensorNegativeTwoQuotient p hp P q).comp (U).toLinearMap
    let hT := actualOriginalCanonicalTensorNegativeTwoTarget_finrank_one p hp P hN
    (actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hT qT ≫
      quotientProjMap (equationIdeal p hp)).ker =
    (actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hN q ≫
      quotientProjMap (equationIdeal p hp)).ker := by
  dsimp only
  let qT := (actualOriginalCanonicalTensorNegativeTwoQuotient p hp P q).comp (U).toLinearMap
  let hT := actualOriginalCanonicalTensorNegativeTwoTarget_finrank_one p hp P hN
  let dT := actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hT qT
  let d := actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hN q
  obtain ⟨e, he⟩ := actualOriginalCanonicalTensorNegativeTwoQuotient_same_nativeJet
    p hp P hP hN q hq
  have hfac : e.hom ≫ (dT ≫ quotientProjMap (equationIdeal p hp)) =
      d ≫ quotientProjMap (equationIdeal p hp) :=
    (Category.assoc e.hom dT (quotientProjMap (equationIdeal p hp))).symm.trans
      (congrArg (fun f => f ≫ quotientProjMap (equationIdeal p hp)) he)
  exact (Scheme.Hom.ker_comp_of_isIso e.hom
    (dT ≫ quotientProjMap (equationIdeal p hp))).symm.trans
      (congrArg (fun f => f.ker) hfac)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual original quadratic vanishes on the literal canonical
negative-two jet exactly when its native conormal coefficient is killed by q. -/
theorem actualOriginalCanonicalTensorNegativeTwoJet_quadratic_mem_iff
    {N : Type u} [AddCommGroup N] [Module κ N]
    (hN : Module.finrank κ N = 1) (q : E →ₗ[κ] N) (hq : Function.Surjective q)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    letI : IsClosedImmersion rP := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let qT := (actualOriginalCanonicalTensorNegativeTwoQuotient p hp P q).comp (U).toLinearMap
    let hT := actualOriginalCanonicalTensorNegativeTwoTarget_finrank_one p hp P hN
    (p3ActualIdealQuadraticIntrinsicLinearEquiv
      (rP ≫ quotientProjMap (equationIdeal p hp)) s).val ∈
      intrinsicFullQuadraticSystem
        (actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hT qT ≫
          quotientProjMap (equationIdeal p hp)) ↔
      q (actualOriginalIdealQuadraticPositiveTwoPhi p hp P hP s) = 0 := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI : IsClosedImmersion rP := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let qT := (actualOriginalCanonicalTensorNegativeTwoQuotient p hp P q).comp (U).toLinearMap
  let hT := actualOriginalCanonicalTensorNegativeTwoTarget_finrank_one p hp P hN
  let dT := actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hT qT
  let d := actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hN q
  obtain ⟨e, he⟩ := actualOriginalCanonicalTensorNegativeTwoQuotient_same_nativeJet
    p hp P hP hN q hq
  have hfac : e.hom ≫ (dT ≫ quotientProjMap (equationIdeal p hp)) =
      d ≫ quotientProjMap (equationIdeal p hp) :=
    (Category.assoc e.hom dT (quotientProjMap (equationIdeal p hp))).symm.trans
      (congrArg (fun f => f ≫ quotientProjMap (equationIdeal p hp)) he)
  have hsystem : intrinsicFullQuadraticSystem (dT ≫ quotientProjMap (equationIdeal p hp)) =
      intrinsicFullQuadraticSystem (d ≫ quotientProjMap (equationIdeal p hp)) :=
    (intrinsicFullQuadraticSystem_comp_isIso e.hom
      (dT ≫ quotientProjMap (equationIdeal p hp))).symm.trans
        (congrArg intrinsicFullQuadraticSystem hfac)
  have hmem :
      (p3ActualIdealQuadraticIntrinsicLinearEquiv
        (rP ≫ quotientProjMap (equationIdeal p hp)) s).val ∈
        intrinsicFullQuadraticSystem (dT ≫ quotientProjMap (equationIdeal p hp)) ↔
      (p3ActualIdealQuadraticIntrinsicLinearEquiv
        (rP ≫ quotientProjMap (equationIdeal p hp)) s).val ∈
        intrinsicFullQuadraticSystem (d ≫ quotientProjMap (equationIdeal p hp)) := by
    rw [hsystem]
  exact hmem.trans (canonicalNegativeTwoArbitraryTarget_quadratic_mem_iff p hp P hP hN q s)

end
end PfaffianDescent

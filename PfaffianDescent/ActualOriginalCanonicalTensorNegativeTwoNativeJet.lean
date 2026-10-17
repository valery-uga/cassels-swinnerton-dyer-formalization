import PfaffianDescent.ActualFieldPointCanonicalInverseTwistFrameComparison
import PfaffianDescent.ActualOriginalCanonicalTensorNegativeTwoQuotient
import PfaffianDescent.ActualOriginalPositiveTwoArbitraryTargetCorrespondence

/-! SOURCE ONLY / UNVERIFIED. The manuscript's literal canonical tensor
negative-two representative gives the SAME original native jet up to an
internally derived target/source Iso. Every surjective quotient onto every
actual one-dimensional target is retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K : Type u} [Field K]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  (P : closedPoints (hypersurface p hp))
local notation "κ" => CommRingCat.carrier (Scheme.residueField (hypersurface p hp) (Subtype.val P))
local notation "rP" => Scheme.fromSpecResidueField (hypersurface p hp) (Subtype.val P)
local notation "E" => ModuleCat.carrier (ActualOriginalPositiveTwoFiber p hp P)
local notation "W" => ModuleCat.carrier
  (Functor.obj (moduleSpecΓFunctor (R := CommRingCat.of κ))
    (Functor.obj (Scheme.Modules.pullback rP) (schemeRelativeDifferentials (hypersurfaceToBase p hp))))
local notation "B" => ModuleCat.carrier
  (ActualFieldPointNegativeTwistFiber (K := K) (L := κ) (equationIdeal p hp) rP 2)
local notation "alpha" => actualFieldPointCanonicalTwistPairingScalar (K := K) (L := κ)
  (equationIdeal p hp) rP 2
local notation "U" => actualCubicPositiveTwoDifferentialPointFiberEquiv (K := K) (L := κ) p hp rP

private def canonicalNegativeTargetEquiv
    (N : Type u) [AddCommGroup N] [Module κ N] : N ⊗[κ] B ≃ₗ[κ] N :=
  TensorProduct.congr (LinearEquiv.refl κ N)
    (actualFieldPointNegativeTwistFiberEquiv (K := K) (L := κ)
      (equationIdeal p hp) rP 2) ≪≫ₗ TensorProduct.rid κ N

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full canonical contraction coefficient is derived, not supplied. -/
theorem actualOriginalCanonicalTensorNegativeTwoQuotient_contract
    {N : Type u} [AddCommGroup N] [Module κ N] (q : E →ₗ[κ] N) (w : W) :
    let t := (TensorProduct.congr (LinearEquiv.refl κ N)
      (actualFieldPointNegativeTwistFiberEquiv (K := K) (L := κ)
        (equationIdeal p hp) rP 2)) ≪≫ₗ TensorProduct.rid κ N
    t (actualOriginalCanonicalTensorNegativeTwoQuotient p hp P q w) =
      alpha⁻¹ • q ((U).symm w) := by
  exact actualFieldPointCanonicalTensorQuotient_contract (K := K) (L := κ)
    (equationIdeal p hp) rP (schemeRelativeDifferentials (hypersurfaceToBase p hp)) 2 q w

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensoring by the ACTUAL negative-two fiber with the ACTUAL canonical
pairing yields the same native jet class at the SAME original quartic
point. Its nonzero comparison scalar and all line/quotient properties are
internally derived, and no desired comparison certificate is assumed. -/
theorem actualOriginalCanonicalTensorNegativeTwoQuotient_same_nativeJet
    [PerfectField K] (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    {N : Type u} [AddCommGroup N] [Module κ N]
    (hN : Module.finrank κ N = 1) (q : E →ₗ[κ] N) (hq : Function.Surjective q) :
    let qT := (actualOriginalCanonicalTensorNegativeTwoQuotient p hp P q).comp (U).toLinearMap
    let hT := actualOriginalCanonicalTensorNegativeTwoTarget_finrank_one p hp P hN
    ∃ e : Spec (.of (DualNumber κ)) ≅ Spec (.of (DualNumber κ)),
      e.hom ≫ actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hT qT =
        actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hN q := by
  let qT := (actualOriginalCanonicalTensorNegativeTwoQuotient p hp P q).comp (U).toLinearMap
  let t := canonicalNegativeTargetEquiv p hp P N
  let hT := actualOriginalCanonicalTensorNegativeTwoTarget_finrank_one p hp P hN
  have ha : alpha ≠ 0 := actualFieldPointCanonicalTwistPairingScalar_ne_zero (K := K) (L := κ)
    (equationIdeal p hp) rP 2
  let scale := LinearEquiv.smulOfNeZero κ N alpha⁻¹ (inv_ne_zero ha)
  let targetIso : N ≃ₗ[κ] N ⊗[κ] B := scale ≪≫ₗ t.symm
  have hqT : Function.Surjective qT :=
    (actualOriginalCanonicalTensorNegativeTwoQuotient_surjective p hp P q hq).comp (U).surjective
  have hqT_eq : qT = targetIso.toLinearMap.comp q := by
    apply LinearMap.ext
    intro x
    apply t.injective
    have hx := actualOriginalCanonicalTensorNegativeTwoQuotient_contract p hp P q (U x)
    have hx' : t (qT x) = alpha⁻¹ • q x := by
      simpa only [qT, t, LinearMap.comp_apply, (U).symm_apply_apply,
        canonicalNegativeTargetEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_coe] using hx
    have htarget : t ((targetIso.toLinearMap.comp q) x) = scale (q x) := by
      change t (t.symm (scale (q x))) = scale (q x)
      exact t.apply_symm_apply (scale (q x))
    have hscale : scale (q x) = alpha⁻¹ • q x := by
      simp only [scale, LinearEquiv.smulOfNeZero_apply]
    exact hx'.trans (htarget.trans hscale).symm
  exact (actualOriginalPositiveTwoArbitraryTargetJetEmbedding_overIso_iff
    p hp P hP hN hT q qT hq hqT).mpr ⟨targetIso, hqT_eq⟩

end
end PfaffianDescent

import PfaffianDescent.ActualFieldPointNegativeTwistUnitIso
import PfaffianDescent.ActualCubicPositiveTwoDifferentialPointFiber
import PfaffianDescent.ActualOriginalPositiveTwoArbitraryTargetCorrespondence
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! SOURCE ONLY / UNVERIFIED. An internally derived-frame representative of
literal q tensor id on the ACTUAL native negative-two fiber. The source map
is q-independent. Canonical positive-negative pairing fidelity is a separate
REQUIRED obligation; this module does not assert that additional equality. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem negativeFiberTensor_contraction
    {L E B N : Type u} [Field L]
    [AddCommGroup E] [Module L E] [AddCommGroup B] [Module L B]
    [AddCommGroup N] [Module L N] (b : B ≃ₗ[L] L) (q : E →ₗ[L] N) (x : E) :
    ((TensorProduct.congr (LinearEquiv.refl L N) b) ≪≫ₗ TensorProduct.rid L N)
      (TensorProduct.map q (LinearMap.id : B →ₗ[L] B)
        (x ⊗ₜ[L] b.symm 1)) = q x := by
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, b.apply_symm_apply,
    TensorProduct.rid_tmul, one_smul]

section
variable {K : Type u} [Field K]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  (P : closedPoints (hypersurface p hp))
local notation "L" => (hypersurface p hp).residueField P.1
local notation "rP" => (hypersurface p hp).fromSpecResidueField P.1
local notation "E" => ActualOriginalPositiveTwoFiber p hp P
local notation "W" => (moduleSpecΓFunctor (R := .of L)).obj
  ((Scheme.Modules.pullback rP).obj (schemeRelativeDifferentials (hypersurfaceToBase p hp)))
local notation "B" => ActualFieldPointNegativeTwistFiber (equationIdeal p hp) rP 2

def actualOriginalTensorNegativeTwoSourceEquiv : W ≃ₗ[L] E ⊗[L] B :=
  (actualCubicPositiveTwoDifferentialPointFiberEquiv (K := K) (L := L) p hp rP).symm ≪≫ₗ
    (TensorProduct.rid L E).symm ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl L E)
        (actualFieldPointNegativeTwistFiberEquiv (K := K) (L := L)
          (equationIdeal p hp) rP 2).symm

def actualOriginalTensorNegativeTwoTargetEquiv
    (N : Type u) [AddCommGroup N] [Module L N] : N ⊗[L] B ≃ₗ[L] N :=
  TensorProduct.congr (LinearEquiv.refl L N)
    (actualFieldPointNegativeTwistFiberEquiv (K := K) (L := L)
      (equationIdeal p hp) rP 2) ≪≫ₗ TensorProduct.rid L N

def actualOriginalTensorNegativeTwoQuotient
    {N : Type u} [AddCommGroup N] [Module L N] (q : E →ₗ[L] N) :
    W →ₗ[L] N ⊗[L] B :=
  (TensorProduct.map q (LinearMap.id : B →ₗ[L] B)).comp
    (actualOriginalTensorNegativeTwoSourceEquiv p hp P).toLinearMap

theorem actualOriginalTensorNegativeTwoQuotient_contract
    {N : Type u} [AddCommGroup N] [Module L N] (q : E →ₗ[L] N) (w : W) :
    actualOriginalTensorNegativeTwoTargetEquiv p hp P N
      (actualOriginalTensorNegativeTwoQuotient p hp P q w) =
        q ((actualCubicPositiveTwoDifferentialPointFiberEquiv
          (K := K) (L := L) p hp rP).symm w) := by
  simpa only [actualOriginalTensorNegativeTwoQuotient,
    actualOriginalTensorNegativeTwoSourceEquiv, actualOriginalTensorNegativeTwoTargetEquiv,
    LinearMap.comp_apply, LinearEquiv.trans_apply, TensorProduct.rid_symm_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply] using
      negativeFiberTensor_contraction
        (actualFieldPointNegativeTwistFiberEquiv (K := K) (L := L)
          (equationIdeal p hp) rP 2) q
        ((actualCubicPositiveTwoDifferentialPointFiberEquiv
          (K := K) (L := L) p hp rP).symm w)

theorem actualOriginalTensorNegativeTwoQuotient_surjective
    {N : Type u} [AddCommGroup N] [Module L N] (q : E →ₗ[L] N)
    (hq : Function.Surjective q) :
    Function.Surjective (actualOriginalTensorNegativeTwoQuotient p hp P q) := by
  let U := actualCubicPositiveTwoDifferentialPointFiberEquiv (K := K) (L := L) p hp rP
  let t := actualOriginalTensorNegativeTwoTargetEquiv p hp P N
  intro y
  obtain ⟨x, hx⟩ := hq (t y)
  refine ⟨U x, ?_⟩
  apply t.injective
  rw [actualOriginalTensorNegativeTwoQuotient_contract, U.symm_apply_apply, hx]

theorem actualOriginalTensorNegativeTwoTarget_finrank_one
    {N : Type u} [AddCommGroup N] [Module L N] (hN : Module.finrank L N = 1) :
    Module.finrank L (N ⊗[L] B) = 1 :=
  (actualOriginalTensorNegativeTwoTargetEquiv p hp P N).finrank_eq.trans hN

/-- The same native jet class is retained after the actual negative-fiber
representative and its derived-frame source identification. This does not
assert the still-required canonical inverse-pairing source identification. -/
theorem actualOriginalTensorNegativeTwoQuotient_same_nativeJet
    [PerfectField K] (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)
    {N : Type u} [AddCommGroup N] [Module L N]
    (hN : Module.finrank L N = 1) (q : E →ₗ[L] N) (hq : Function.Surjective q) :
    let U := actualCubicPositiveTwoDifferentialPointFiberEquiv (K := K) (L := L) p hp rP
    let qT := (actualOriginalTensorNegativeTwoQuotient p hp P q).comp U.toLinearMap
    let hT := actualOriginalTensorNegativeTwoTarget_finrank_one p hp P hN
    ∃ e : Spec (.of (DualNumber L)) ≅ Spec (.of (DualNumber L)),
      e.hom ≫ actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hT qT =
        actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hN q := by
  let U := actualCubicPositiveTwoDifferentialPointFiberEquiv (K := K) (L := L) p hp rP
  let qT := (actualOriginalTensorNegativeTwoQuotient p hp P q).comp U.toLinearMap
  let t := actualOriginalTensorNegativeTwoTargetEquiv p hp P N
  let hT := actualOriginalTensorNegativeTwoTarget_finrank_one p hp P hN
  have hqT : Function.Surjective qT :=
    (actualOriginalTensorNegativeTwoQuotient_surjective p hp P q hq).comp U.surjective
  have hqT_eq : qT = t.symm.toLinearMap.comp q := by
    apply LinearMap.ext
    intro x
    apply t.injective
    have hx := actualOriginalTensorNegativeTwoQuotient_contract p hp P q (U x)
    simpa only [qT, LinearMap.comp_apply, U.symm_apply_apply,
      LinearEquiv.coe_coe, t.apply_symm_apply] using hx
  exact (actualOriginalPositiveTwoArbitraryTargetJetEmbedding_overIso_iff
    p hp P hP hN hT q qT hq hqT).mpr ⟨t.symm, hqT_eq⟩

end
end PfaffianDescent

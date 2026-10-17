import PfaffianDescent.ActualKaehlerLineDualAlgebra

/- SOURCE ONLY / UNVERIFIED. Construct the actual epsilon fiber line with
the ORIGINAL residue algebra structure. Reduction compatibility is ordinary
algebra data in this helper; the native caller derives it on chart generators. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct KaehlerDifferential TrivSqZeroExt
open scoped TensorProduct
universe u
variable {K R L : Type u} [Field K] [CommRing R] [Field L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

def residueCompatibleActualDualEpsilonDerivation
    (phi : R →ₐ[K] DualNumber L)
    (hred : ∀ r, (phi r).fst = algebraMap R L r) : Derivation K R L where
  toLinearMap :=
    { toFun := fun r => (phi r).snd
      map_add' := by intro a b; rw [map_add, snd_add]
      map_smul' := by intro c a; rw [map_smul, snd_smul]; rfl }
  map_one_eq_zero' := by
    change (phi (1 : R)).snd = 0
    rw [map_one]
    rfl
  leibniz' a b := by
    change (phi (a * b)).snd = a • (phi b).snd + b • (phi a).snd
    simp only [Algebra.smul_def]
    rw [map_mul, DualNumber.snd_mul, hred a, hred b]
    ring

def residueCompatibleActualDualFiberLine
    (phi : R →ₐ[K] DualNumber L)
    (hred : ∀ r, (phi r).fst = algebraMap R L r) :
    L ⊗[R] KaehlerDifferential K R →ₗ[L] L :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton L _
      (residueCompatibleActualDualEpsilonDerivation phi hred).liftKaehlerDifferential)

lemma residueCompatibleActualDualFiberLine_tmul_D
    (phi : R →ₐ[K] DualNumber L)
    (hred : ∀ r, (phi r).fst = algebraMap R L r) (c : L) (r : R) :
    residueCompatibleActualDualFiberLine phi hred
      (c ⊗ₜ[R] KaehlerDifferential.D K R r) = c * (phi r).snd := by
  change c • (residueCompatibleActualDualEpsilonDerivation phi hred).liftKaehlerDifferential
    (KaehlerDifferential.D K R r) = _
  rw [Derivation.liftKaehlerDifferential_comp_D]
  rfl

lemma residueCompatibleActualDualFiberLine_surjective
    (phi : R →ₐ[K] DualNumber L)
    (hred : ∀ r, (phi r).fst = algebraMap R L r) (hphi : Function.Surjective phi) :
    Function.Surjective (residueCompatibleActualDualFiberLine phi hred) := by
  intro c
  obtain ⟨r, hr⟩ := hphi (inr c)
  refine ⟨1 ⊗ₜ[R] KaehlerDifferential.D K R r, ?_⟩
  rw [residueCompatibleActualDualFiberLine_tmul_D, hr]
  simp

lemma residueCompatibleActualDualFiberLine_reconstruct
    (phi : R →ₐ[K] DualNumber L)
    (hred : ∀ r, (phi r).fst = algebraMap R L r) :
    actualKaehlerLineDualAlgebraMap (residueCompatibleActualDualFiberLine phi hred) = phi := by
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · exact (actualKaehlerLineDualAlgebraMap_fst _ r).trans (hred r).symm
  · rw [actualKaehlerLineDualAlgebraMap_snd,
      residueCompatibleActualDualFiberLine_tmul_D, one_mul]

end PfaffianDescent

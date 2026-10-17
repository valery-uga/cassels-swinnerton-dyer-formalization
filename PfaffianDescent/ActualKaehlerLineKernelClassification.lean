import PfaffianDescent.ResidueCompatibleDualKernelClassification
import PfaffianDescent.ResidueCompatibleActualDualMorphismLine
import PfaffianDescent.ActualKaehlerLineDualSurjectivity

/-! SOURCE ONLY / UNVERIFIED. The two actual constructions between
residue-compatible dual maps and Kaehler-fiber functionals are inverse.
For surjective line quotients at a separable residue, equality of the entire
embedded affine quotient ideal is exactly multiplication by a nonzero
residue scalar. No desired equality is an input hypothesis. -/

noncomputable section
namespace PfaffianDescent
open TensorProduct KaehlerDifferential TrivSqZeroExt
open scoped TensorProduct
universe u
variable {K R L : Type u} [Field K] [CommRing R] [Field L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

theorem actualKaehlerFiberLinearMap_ext
    {q₁ q₂ : L ⊗[R] KaehlerDifferential K R →ₗ[L] L}
    (h : ∀ r, q₁ (1 ⊗ₜ[R] KaehlerDifferential.D K R r) =
      q₂ (1 ⊗ₜ[R] KaehlerDifferential.D K R r)) : q₁ = q₂ := by
  let t₁ := (q₁.restrictScalars R).comp
    (TensorProduct.mk R L (KaehlerDifferential K R) 1)
  let t₂ := (q₂.restrictScalars R).comp
    (TensorProduct.mk R L (KaehlerDifferential K R) 1)
  have ht : t₁ = t₂ := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro r
    exact h r
  apply TensorProduct.AlgebraTensorModule.ext
  intro c omega
  calc
    q₁ (c ⊗ₜ[R] omega) = c • q₁ (1 ⊗ₜ[R] omega) := by
      rw [TensorProduct.tmul_eq_smul_one_tmul c, map_smul]
    _ = c • q₂ (1 ⊗ₜ[R] omega) :=
      congrArg (fun z : L => c • z) (LinearMap.congr_fun ht omega)
    _ = q₂ (c ⊗ₜ[R] omega) := by
      rw [TensorProduct.tmul_eq_smul_one_tmul c, map_smul]

theorem actualKaehlerLineDualAlgebraMap_fiberLine
    (q : L ⊗[R] KaehlerDifferential K R →ₗ[L] L) :
    residueCompatibleActualDualFiberLine (actualKaehlerLineDualAlgebraMap q)
      (actualKaehlerLineDualAlgebraMap_fst q) = q := by
  apply actualKaehlerFiberLinearMap_ext
  intro r
  rw [residueCompatibleActualDualFiberLine_tmul_D,
    actualKaehlerLineDualAlgebraMap_snd, one_mul]

theorem actualKaehlerLineDualAlgebraMap_sameKernel_iff_smul
    [Algebra.IsSeparable K L]
    (hrho : Function.Surjective (algebraMap R L))
    (q₁ q₂ : L ⊗[R] KaehlerDifferential K R →ₗ[L] L)
    (hq₁ : Function.Surjective q₁) (hq₂ : Function.Surjective q₂) :
    RingHom.ker (actualKaehlerLineDualAlgebraMap q₁).toRingHom =
        RingHom.ker (actualKaehlerLineDualAlgebraMap q₂).toRingHom ↔
      ∃ c : L, c ≠ 0 ∧ q₂ = c • q₁ := by
  have hmaps := residueCompatibleSurjectiveDualMaps_sameKernel_iff_rescale
    (actualKaehlerLineDualAlgebraMap q₁) (actualKaehlerLineDualAlgebraMap q₂)
    (actualKaehlerLineDualAlgebraMap_surjective hrho q₁ hq₁)
    (actualKaehlerLineDualAlgebraMap_surjective hrho q₂ hq₂)
    (fun r => (actualKaehlerLineDualAlgebraMap_fst q₁ r).trans
      (actualKaehlerLineDualAlgebraMap_fst q₂ r).symm)
  rw [hmaps]
  constructor
  · rintro ⟨c, hc, hscale⟩
    refine ⟨c, hc, ?_⟩
    apply actualKaehlerFiberLinearMap_ext
    intro r
    have h := congrArg TrivSqZeroExt.snd (hscale r)
    simpa [QuarticNet.dualNumberRescaleEquiv, QuarticNet.dualNumberRescale,
      TrivSqZeroExt.snd_map, LinearMap.mulLeft_apply,
      actualKaehlerLineDualAlgebraMap_snd, LinearMap.smul_apply, smul_eq_mul] using h
  · rintro ⟨c, hc, hq⟩
    refine ⟨c, hc, ?_⟩
    intro r
    apply TrivSqZeroExt.ext
    · simp [QuarticNet.dualNumberRescaleEquiv, QuarticNet.dualNumberRescale,
        TrivSqZeroExt.fst_map]
    · simp [QuarticNet.dualNumberRescaleEquiv, QuarticNet.dualNumberRescale,
        TrivSqZeroExt.snd_map, LinearMap.mulLeft_apply,
        actualKaehlerLineDualAlgebraMap_snd, hq, LinearMap.smul_apply, smul_eq_mul]

end PfaffianDescent

import PfaffianDescent.ActualLengthTwoDualPresentationRescaling
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! SOURCE ONLY / UNVERIFIED. Over a separable residue field, a ground-field
dual-number automorphism fixing the actual residue is exactly nonzero epsilon
rescaling. Consequently surjective residue-compatible maps have the same
ENTIRE ring kernel exactly when they differ by that rescaling. The surjections
here are natural intermediate quotient maps, not extra manuscript premises. -/

noncomputable section
namespace PfaffianDescent
open TrivSqZeroExt
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Algebra.IsSeparable K L]

theorem residueCompatibleDualAlgEquiv_is_rescaling
    (e : DualNumber L ≃ₐ[K] DualNumber L)
    (hred : ∀ z, (e z).fst = z.fst) :
    ∃ (c : L) (hc : c ≠ 0), ∀ z,
      e z = QuarticNet.dualNumberRescaleEquiv c hc z := by
  letI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let red := TrivSqZeroExt.fstHom K L L
  let inc := TrivSqZeroExt.inlAlgHom K L L
  have hnil : IsNilpotent (RingHom.ker red.toRingHom) := by
    refine ⟨2, ?_⟩
    change TrivSqZeroExt.kerIdeal L L ^ 2 = ⊥
    exact TrivSqZeroExt.kerIdeal_sq L L
  have hcoeff : e.toAlgHom.comp inc = inc := by
    apply Algebra.FormallyUnramified.lift_unique' red hnil
    apply AlgHom.ext
    intro a
    exact hred (TrivSqZeroExt.inl a)
  let eL : DualNumber L ≃ₐ[L] DualNumber L :=
    { e.toRingEquiv with
      commutes' := fun a => AlgHom.congr_fun hcoeff a }
  obtain ⟨c, hc, heL⟩ := QuarticNet.dualNumberAlgEquiv_is_actual_rescaling eL
  refine ⟨c, hc, ?_⟩
  intro z
  exact congrArg (fun a : DualNumber L ≃ₐ[L] DualNumber L => a z) heL

theorem residueCompatibleSurjectiveDualMaps_sameKernel_iff_rescale
    {R : Type u} [CommRing R] [Algebra K R]
    (phi₁ phi₂ : R →ₐ[K] DualNumber L)
    (hphi₁ : Function.Surjective phi₁) (hphi₂ : Function.Surjective phi₂)
    (hred : ∀ r, (phi₁ r).fst = (phi₂ r).fst) :
    RingHom.ker phi₁.toRingHom = RingHom.ker phi₂.toRingHom ↔
      ∃ (c : L) (hc : c ≠ 0), ∀ r,
        phi₂ r = QuarticNet.dualNumberRescaleEquiv c hc (phi₁ r) := by
  constructor
  · intro hker
    let f := AlgHom.liftOfSurjective phi₁ hphi₁ phi₂ hker.le
    let g := AlgHom.liftOfSurjective phi₂ hphi₂ phi₁ hker.symm.le
    have hfg : f.comp g = AlgHom.id K (DualNumber L) := by
      apply AlgHom.ext
      intro z
      obtain ⟨r, rfl⟩ := hphi₂ z
      change (AlgHom.liftOfSurjective phi₁ hphi₁ phi₂ hker.le)
          ((AlgHom.liftOfSurjective phi₂ hphi₂ phi₁ hker.symm.le) (phi₂ r)) = phi₂ r
      rw [AlgHom.liftOfSurjective_apply, AlgHom.liftOfSurjective_apply]
    have hgf : g.comp f = AlgHom.id K (DualNumber L) := by
      apply AlgHom.ext
      intro z
      obtain ⟨r, rfl⟩ := hphi₁ z
      change (AlgHom.liftOfSurjective phi₂ hphi₂ phi₁ hker.symm.le)
          ((AlgHom.liftOfSurjective phi₁ hphi₁ phi₂ hker.le) (phi₁ r)) = phi₁ r
      rw [AlgHom.liftOfSurjective_apply, AlgHom.liftOfSurjective_apply]
    let e := AlgEquiv.ofAlgHom f g hfg hgf
    have he (r : R) : e (phi₁ r) = phi₂ r :=
      AlgHom.liftOfSurjective_apply phi₁ hphi₁ phi₂ hker.le r
    have heRed (z : DualNumber L) : (e z).fst = z.fst := by
      obtain ⟨r, rfl⟩ := hphi₁ z
      rw [he]
      exact (hred r).symm
    obtain ⟨c, hc, heScale⟩ := residueCompatibleDualAlgEquiv_is_rescaling e heRed
    exact ⟨c, hc, fun r => (he r).symm.trans (heScale (phi₁ r))⟩
  · rintro ⟨c, hc, hscale⟩
    apply Ideal.ext
    intro r
    change phi₁ r = 0 ↔ phi₂ r = 0
    rw [hscale r]
    constructor
    · intro hr
      rw [hr, map_zero]
    · intro hr
      exact (QuarticNet.dualNumberRescaleEquiv c hc).injective
        (hr.trans (map_zero (QuarticNet.dualNumberRescaleEquiv c hc)).symm)

end PfaffianDescent

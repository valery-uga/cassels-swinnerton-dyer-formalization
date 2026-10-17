import PfaffianDescent.OneDimensionalQuotientTargetIso
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! SOURCE ONLY / UNVERIFIED. Surjective field-valued quotient classes
are internally identified with actual dimension-one subspaces of the dual.
No quotient-class/projective equivalence is an input. -/
noncomputable section
namespace PfaffianDescent
universe u
variable {L V W : Type u} [Field L]
  [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]

private theorem quotientFunctional_ne_zero
    (q : V →ₗ[L] L) (hq : Function.Surjective q) : q ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := hq 1
  simp only [h, LinearMap.zero_apply] at hx
  exact zero_ne_one hx

/-- Transport actual quotient representatives by an actual source equivalence. -/
def surjectiveOneDimensionalQuotientSourceEquiv (e : V ≃ₗ[L] W) :
    {q : V →ₗ[L] L // Function.Surjective q} ≃
      {q : W →ₗ[L] L // Function.Surjective q} where
  toFun q := ⟨q.1.comp e.symm.toLinearMap, q.2.comp e.symm.surjective⟩
  invFun q := ⟨q.1.comp e.toLinearMap, q.2.comp e.surjective⟩
  left_inv q := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change q.1 (e.symm (e x)) = q.1 x
    rw [e.symm_apply_apply]
  right_inv q := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change q.1 (e (e.symm x)) = q.1 x
    rw [e.apply_symm_apply]

/-- The source transport preserves and reflects the actual target-iso relation. -/
def surjectiveOneDimensionalQuotientClasses_sourceEquiv (e : V ≃ₗ[L] W) :
    Quotient (surjectiveOneDimensionalQuotientSetoid L V) ≃
      Quotient (surjectiveOneDimensionalQuotientSetoid L W) := by
  apply Quotient.congr (surjectiveOneDimensionalQuotientSourceEquiv e)
  intro q₁ q₂
  change OneDimensionalQuotientTargetIso q₁.1 q₂.1 ↔
    OneDimensionalQuotientTargetIso
      (q₁.1.comp e.symm.toLinearMap) (q₂.1.comp e.symm.toLinearMap)
  rw [oneDimensionalQuotientTargetIso_iff_smul,
    oneDimensionalQuotientTargetIso_iff_smul]
  constructor
  · rintro ⟨c, hc, hq⟩
    refine ⟨c, hc, ?_⟩
    apply LinearMap.ext
    intro x
    change q₂.1 (e.symm x) = c • q₁.1 (e.symm x)
    exact LinearMap.congr_fun hq (e.symm x)
  · rintro ⟨c, hc, hq⟩
    refine ⟨c, hc, ?_⟩
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hq (e x)
    change q₂.1 (e.symm (e x)) = c • q₁.1 (e.symm (e x)) at hx
    simpa only [e.symm_apply_apply, LinearMap.smul_apply] using hx

/-- A quotient functional defines the actual projective point of the dual. -/
def surjectiveOneDimensionalQuotientClasses_toProjectiveDual :
    Quotient (surjectiveOneDimensionalQuotientSetoid L V) →
      Projectivization L (Module.Dual L V) :=
  Quotient.lift
    (fun q => Projectivization.mk L q.1 (quotientFunctional_ne_zero q.1 q.2))
    (by
      intro q₁ q₂ h
      obtain ⟨c, hc, hq⟩ := (oneDimensionalQuotientTargetIso_iff_smul q₁.1 q₂.1).mp h
      exact ((Projectivization.mk_eq_mk_iff' L q₂.1 q₁.1
        (quotientFunctional_ne_zero q₂.1 q₂.2)
        (quotientFunctional_ne_zero q₁.1 q₁.2)).mpr ⟨c, hq.symm⟩).symm)

private theorem quotientClasses_toProjectiveDual_injective :
    Function.Injective (surjectiveOneDimensionalQuotientClasses_toProjectiveDual
      (L := L) (V := V)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro q₁ q₂ h
  change Projectivization.mk L q₁.1 (quotientFunctional_ne_zero q₁.1 q₁.2) =
    Projectivization.mk L q₂.1 (quotientFunctional_ne_zero q₂.1 q₂.2) at h
  obtain ⟨c, hq⟩ := (Projectivization.mk_eq_mk_iff' L q₂.1 q₁.1
    (quotientFunctional_ne_zero q₂.1 q₂.2)
    (quotientFunctional_ne_zero q₁.1 q₁.2)).mp h.symm
  have hc : c ≠ 0 := by
    intro hc
    apply quotientFunctional_ne_zero q₂.1 q₂.2
    rw [← hq, hc, zero_smul]
  apply Quotient.sound
  exact (oneDimensionalQuotientTargetIso_iff_smul q₁.1 q₂.1).mpr ⟨c, hc, hq.symm⟩

private theorem quotientClasses_toProjectiveDual_surjective :
    Function.Surjective (surjectiveOneDimensionalQuotientClasses_toProjectiveDual
      (L := L) (V := V)) := by
  intro z
  let q : {q : V →ₗ[L] L // Function.Surjective q} :=
    ⟨z.rep, LinearMap.surjective z.rep_nonzero⟩
  refine ⟨Quotient.mk (surjectiveOneDimensionalQuotientSetoid L V) q, ?_⟩
  change Projectivization.mk L z.rep _ = z
  exact Projectivization.mk_rep z

/-- Derived equivalence, including both projective-dual directions. -/
def surjectiveOneDimensionalQuotientClasses_projectiveDualEquiv :
    Quotient (surjectiveOneDimensionalQuotientSetoid L V) ≃
      Projectivization L (Module.Dual L V) :=
  Equiv.ofBijective surjectiveOneDimensionalQuotientClasses_toProjectiveDual
    ⟨quotientClasses_toProjectiveDual_injective,
      quotientClasses_toProjectiveDual_surjective⟩

/-- Literal lines are dimension-one submodules of the SAME actual dual. -/
def surjectiveOneDimensionalQuotientClasses_dualLineEquiv :
    Quotient (surjectiveOneDimensionalQuotientSetoid L V) ≃
      {H : Submodule L (Module.Dual L V) // Module.finrank L H = 1} :=
  surjectiveOneDimensionalQuotientClasses_projectiveDualEquiv.trans
    (Projectivization.equivSubmodule L (Module.Dual L V))

end PfaffianDescent

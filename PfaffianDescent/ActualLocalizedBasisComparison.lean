import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Module

/- SOURCE ONLY / UNVERIFIED. Abstract localization comparison and its
naturality. In an actual affine caller the module actions/localization
instances are supplied by canonical structure restriction and formally
etale Kaehler maps, not by a desired sheaf comparison certificate. -/
noncomputable section
namespace PfaffianDescent
universe u

/-- The canonical comparison of two localizations has the actual local
coefficient-ring linearity, derived from localization rather than assumed. -/
def actualLocalizedBasisLinearEquiv
    {R M P N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N]
    (S : Submonoid R) (A : Type u) [CommRing A] [Algebra R A]
    [IsLocalization S A]
    [Module A P] [IsScalarTower R A P]
    [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] P) (g : M →ₗ[R] N)
    [IsLocalizedModule S f] [IsLocalizedModule S g] : P ≃ₗ[A] N := by
  let e := IsLocalizedModule.linearEquiv S f g
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' := fun a x =>
        (e.toLinearMap.extendScalarsOfIsLocalization S A).map_smul a x }

lemma actualLocalizedBasisLinearEquiv_on_source
    {R M P N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N]
    (S : Submonoid R) (A : Type u) [CommRing A] [Algebra R A]
    [IsLocalization S A]
    [Module A P] [IsScalarTower R A P]
    [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] P) (g : M →ₗ[R] N)
    [IsLocalizedModule S f] [IsLocalizedModule S g] (m : M) :
    actualLocalizedBasisLinearEquiv S A f g (f m) = g m :=
  IsLocalizedModule.linearEquiv_apply S f g m

/-- Every denominator acts invertibly on every genuine module over the
localized coefficient ring. No invertibility certificate is supplied. -/
lemma actualLocalizedBasis_denominator_end_unit
    {R : Type u} [CommRing R] (S : Submonoid R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]
    (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (s : S) :
    IsUnit (algebraMap R (Module.End R N) s) := by
  apply (Module.End.isUnit_iff _).mpr
  change Function.Bijective (fun n : N => (s : R) • n)
  have h : (fun n : N => algebraMap R A (s : R) • n) =
      (fun n : N => (s : R) • n) :=
    funext (fun n => IsScalarTower.algebraMap_smul A (s : R) n)
  exact h ▸ (IsLocalization.map_units A s).smul_bijective

/-- Canonical comparisons commute with restrictions solely by localization
uniqueness and the genuine top-restriction identities. The target carries
its source-open ring action through the actual ring restriction. -/
lemma actualLocalizedBasisComparison_naturality
    {R M P₁ P₂ N₁ N₂ : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup P₁] [Module R P₁]
    [AddCommGroup P₂] [Module R P₂]
    [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    (S₁ S₂ : Submonoid R)
    (f₁ : M →ₗ[R] P₁) (f₂ : M →ₗ[R] P₂)
    (g₁ : M →ₗ[R] N₁) (g₂ : M →ₗ[R] N₂)
    [IsLocalizedModule S₁ f₁] [IsLocalizedModule S₂ f₂]
    [IsLocalizedModule S₁ g₁] [IsLocalizedModule S₂ g₂]
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S₁ A]
    [Module A N₂] [IsScalarTower R A N₂]
    (rho : P₁ →ₗ[R] P₂) (nu : N₁ →ₗ[R] N₂)
    (hf : rho.comp f₁ = f₂) (hg : nu.comp g₁ = g₂) :
    (IsLocalizedModule.linearEquiv S₂ f₂ g₂).toLinearMap.comp rho =
      nu.comp (IsLocalizedModule.linearEquiv S₁ f₁ g₁).toLinearMap := by
  apply IsLocalizedModule.ext S₁ f₁
    (fun s => actualLocalizedBasis_denominator_end_unit S₁ A N₂ s)
  apply LinearMap.ext
  intro m
  change IsLocalizedModule.linearEquiv S₂ f₂ g₂ (rho (f₁ m)) =
    nu (IsLocalizedModule.linearEquiv S₁ f₁ g₁ (f₁ m))
  exact (congrArg (fun x => IsLocalizedModule.linearEquiv S₂ f₂ g₂ x)
    (LinearMap.congr_fun hf m)).trans
      ((IsLocalizedModule.linearEquiv_apply S₂ f₂ g₂ m).trans
        ((LinearMap.congr_fun hg m).symm.trans
          (congrArg (fun x => nu x)
            (IsLocalizedModule.linearEquiv_apply S₁ f₁ g₁ m).symm)))

/-- Any actual component map that agrees on the canonical original module
is automatically bijective. This is a primitive localization criterion. -/
lemma actualLocalizedBasisMap_bijective
    {R M P N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N]
    (S : Submonoid R) (f : M →ₗ[R] P) (g : M →ₗ[R] N)
    [IsLocalizedModule S f] [IsLocalizedModule S g]
    (a : P →ₗ[R] N) (ha : a.comp f = g) : Function.Bijective a := by
  have he : a = (IsLocalizedModule.linearEquiv S f g).toLinearMap := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    apply LinearMap.ext
    intro m
    exact (LinearMap.congr_fun ha m).trans
      (IsLocalizedModule.linearEquiv_apply S f g m).symm
  exact he.symm ▸ (IsLocalizedModule.linearEquiv S f g).bijective

end PfaffianDescent

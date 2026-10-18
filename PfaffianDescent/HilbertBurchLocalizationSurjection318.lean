import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Away.Basic

/-!
An original surjection induces an actual surjection after localization
whenever its denominators map onto the target denominators. Its kernel
is the localized original kernel. The principal specialization applies to
any chosen lift of the element defining a physical principal open.
-/

noncomputable section

namespace PfaffianDescent

section General

variable {R Rₗ C Cₗ : Type*}
  [CommRing R] [CommRing Rₗ] [CommRing C] [CommRing Cₗ]
  [Algebra R Rₗ] [Algebra C Cₗ]

def actualLocalizedMap022 (π : R →+* C)
    (M : Submonoid R) (N : Submonoid C)
    [IsLocalization M Rₗ] [IsLocalization N Cₗ]
    (hMN : M.map π = N) : Rₗ →+* Cₗ :=
  IsLocalization.map Cₗ π (hMN.symm ▸ M.le_comap_map)

@[simp] theorem actualLocalizedMap_algebraMap022 (π : R →+* C)
    (M : Submonoid R) (N : Submonoid C)
    [IsLocalization M Rₗ] [IsLocalization N Cₗ]
    (hMN : M.map π = N) (x : R) :
    actualLocalizedMap022 (Rₗ := Rₗ) (Cₗ := Cₗ) π M N hMN
        (algebraMap R Rₗ x) = algebraMap C Cₗ (π x) := by
  exact IsLocalization.map_eq _ x

theorem actualLocalizedMap_surjective022 (π : R →+* C)
    (hπ : Function.Surjective π)
    (M : Submonoid R) (N : Submonoid C)
    [IsLocalization M Rₗ] [IsLocalization N Cₗ]
    (hMN : M.map π = N) :
    Function.Surjective (actualLocalizedMap022 (Rₗ := Rₗ) (Cₗ := Cₗ) π M N hMN) := by
  letI : IsLocalization (M.map π) Cₗ := hMN.symm ▸ inferInstance
  exact IsLocalization.map_surjective_of_surjective
    (M := M) (S := Rₗ) (Q := Cₗ) (g := π) hπ

theorem actualLocalizedMap_ker022 (π : R →+* C)
    (M : Submonoid R) (N : Submonoid C)
    [IsLocalization M Rₗ] [IsLocalization N Cₗ]
    (hMN : M.map π = N) :
    RingHom.ker (actualLocalizedMap022 (Rₗ := Rₗ) (Cₗ := Cₗ) π M N hMN) =
      (RingHom.ker π).map (algebraMap R Rₗ) := by
  exact IsLocalization.ker_map (M := M) (S := Rₗ) Cₗ π hMN

theorem actualLocalizedMap_coefficient_ker022
    {B : Type*} [CommRing B] [Algebra B R] [Algebra B Rₗ]
    [IsScalarTower B R Rₗ]
    (I : Ideal B) (π : R →+* C)
    (hker : RingHom.ker π = I.map (algebraMap B R))
    (M : Submonoid R) (N : Submonoid C)
    [IsLocalization M Rₗ] [IsLocalization N Cₗ]
    (hMN : M.map π = N) :
    RingHom.ker (actualLocalizedMap022 (Rₗ := Rₗ) (Cₗ := Cₗ) π M N hMN) =
      I.map (algebraMap B Rₗ) := by
  rw [actualLocalizedMap_ker022, hker, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

end General

def actualAwayMap022
    {R C : Type*} [CommRing R] [CommRing C]
    (π : R →+* C) (r : R) (s : C) (hrs : π r = s) :
    Localization.Away r →+* Localization.Away s :=
  actualLocalizedMap022 π (Submonoid.powers r) (Submonoid.powers s)
    (by rw [Submonoid.map_powers, hrs])

@[simp] theorem actualAwayMap_algebraMap022
    {R C : Type*} [CommRing R] [CommRing C]
    (π : R →+* C) (r : R) (s : C) (hrs : π r = s) (x : R) :
    actualAwayMap022 π r s hrs (algebraMap R (Localization.Away r) x) =
      algebraMap C (Localization.Away s) (π x) := by
  exact actualLocalizedMap_algebraMap022 π _ _ _ x

theorem actualAwayMap_surjective022
    {R C : Type*} [CommRing R] [CommRing C]
    (π : R →+* C) (hπ : Function.Surjective π)
    (r : R) (s : C) (hrs : π r = s) :
    Function.Surjective (actualAwayMap022 π r s hrs) := by
  exact actualLocalizedMap_surjective022 π hπ _ _ _

theorem actualAwayMap_ker022
    {R C : Type*} [CommRing R] [CommRing C]
    (π : R →+* C) (r : R) (s : C) (hrs : π r = s) :
    RingHom.ker (actualAwayMap022 π r s hrs) =
      (RingHom.ker π).map (algebraMap R (Localization.Away r)) := by
  exact actualLocalizedMap_ker022 π _ _ _

theorem actualAwayMap_coefficient_ker022
    {B R C : Type*} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R]
    (I : Ideal B) (π : R →+* C)
    (hker : RingHom.ker π = I.map (algebraMap B R))
    (r : R) (s : C) (hrs : π r = s) :
    RingHom.ker (actualAwayMap022 π r s hrs) =
      I.map (algebraMap B (Localization.Away r)) := by
  letI : IsScalarTower B R (Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact actualLocalizedMap_coefficient_ker022 I π hker _ _ _

def actualAwayAlgHom022
    {B R C : Type*} [CommRing B] [CommRing R] [CommRing C]
    [Algebra B R] [Algebra B C]
    (π : R →ₐ[B] C) (r : R) (s : C) (hrs : π r = s) :
    Localization.Away r →ₐ[B] Localization.Away s where
  __ := actualAwayMap022 π.toRingHom r s hrs
  commutes' b := by
    letI : IsScalarTower B R (Localization.Away r) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower B C (Localization.Away s) :=
      IsScalarTower.of_algebraMap_eq' rfl
    change actualAwayMap022 π.toRingHom r s hrs
      (algebraMap B (Localization.Away r) b) =
        algebraMap B (Localization.Away s) b
    rw [IsScalarTower.algebraMap_apply B R (Localization.Away r)]
    exact (actualAwayMap_algebraMap022 π.toRingHom r s hrs
      (algebraMap B R b)).trans (by
        exact (congrArg (algebraMap C (Localization.Away s)) (π.commutes b)).trans
          (IsScalarTower.algebraMap_apply B C (Localization.Away s) b).symm)

end PfaffianDescent

end

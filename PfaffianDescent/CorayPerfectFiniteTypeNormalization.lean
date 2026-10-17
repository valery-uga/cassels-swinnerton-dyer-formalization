import PfaffianDescent.CorayPerfectIntegralClosureModuleFinite
import PfaffianDescent.CorayFiniteTypeNormalization

/-! SOURCE ONLY / UNVERIFIED. Construct the ACTUAL localized fraction
extension of the original finite normal base, derive all original K towers,
apply the genuine power-root argument, and transfer to canonical FractionRing
A. Original finite-type perfect K algebra constructs its own polynomial base.
No CharZero/separability/exponent/finite-normalization premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open Algebra Module
open scoped nonZeroDivisors

/-- Actual finite normal-base localization constructs all fraction-field
and original K tower data needed by the inseparable integral-closure proof. -/
theorem perfectField_finiteNormalization_of_finite_normal_base
    (K B A : Type*) [Field K] [PerfectField K]
    [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
    [IsNoetherianRing B] [IsIntegrallyClosed B]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra B A]
    [IsScalarTower K B A] [FaithfulSMul B A] [Module.Finite B A] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  let N : Submonoid A := Algebra.algebraMapSubmonoid A B⁰
  let F := FractionRing B
  let C := Localization N
  have hN : N ≤ A⁰ := by
    rintro a ⟨b, hb, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B A)).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp hb))
  letI : IsDomain C := IsLocalization.isDomain_localization hN
  letI : Module.Finite F C := Module.Finite.of_isLocalization B A B⁰
  letI : Algebra.IsIntegral F C := inferInstance
  have hCfield : IsField C := isField_of_isIntegral_of_isField' (R := F) (S := C)
    (Field.toIsField F)
  letI : Field C := hCfield.toField
  letI : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr
    (IsLocalization.injective C hN)
  letI : IsFractionRing A C := IsLocalization.of_le (M := N) A⁰ hN (fun r hr =>
    isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A C)).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp hr)))
  letI : IsScalarTower K B F :=
    inferInstanceAs (IsScalarTower K B (FractionRing B))
  letI : IsScalarTower K A C :=
    inferInstanceAs (IsScalarTower K A (Localization N))
  letI : IsScalarTower K B C := by
    apply IsScalarTower.of_algebraMap_eq
    intro k
    change algebraMap A C (algebraMap K A k) =
      algebraMap B C (algebraMap K B k)
    rw [IsScalarTower.algebraMap_apply K B A]
    exact (IsScalarTower.algebraMap_apply B A C (algebraMap K B k)).symm
  letI : IsScalarTower K F C := by
    apply IsScalarTower.of_algebraMap_eq
    intro k
    calc
      algebraMap K C k = algebraMap B C (algebraMap K B k) :=
        IsScalarTower.algebraMap_apply K B C k
      _ = algebraMap F C (algebraMap B F (algebraMap K B k)) :=
        IsScalarTower.algebraMap_apply B F C (algebraMap K B k)
      _ = algebraMap F C (algebraMap K F k) := rfl
  letI : Module.Finite A (integralClosure A C) :=
    perfectField_integralClosure_finite_of_finite_normal_base K B F C A
  exact Module.Finite.equiv
    ((FractionRing.algEquiv (A := A) C).symm.mapIntegralClosure.toLinearEquiv)

/-- The SAME canonical normalization ring of every original finite-type
K-domain is finite over A for original perfect K, with no added separability
or finite-normalization input. The polynomial base is constructed internally. -/
theorem finiteNormalization_of_finiteType_perfectField
    (K A : Type*) [Field K] [PerfectField K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  obtain ⟨n, g, hginj, hgfinite⟩ := exists_finite_inj_algHom_of_fg K A
  let B := MvPolynomial (Fin n) K
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsScalarTower K B A :=
    IsScalarTower.of_algebraMap_eq fun k => (g.commutes k).symm
  letI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hginj
  letI : Module.Finite B A := by
    change g.toRingHom.Finite at hgfinite
    exact (RingHom.finite_algebraMap).mp hgfinite
  exact perfectField_finiteNormalization_of_finite_normal_base K B A

end PfaffianDescent.Coray

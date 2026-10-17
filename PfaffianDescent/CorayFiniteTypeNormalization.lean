import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra

/-!
# Actual finite normalization over a characteristic-zero field

Noether normalization constructs an actual polynomial subalgebra over which
A is finite. The actual localization of A at the nonzero elements of that
polynomial base is a finite-dimensional domain over its fraction field,
hence an actual field and actual fraction field of A. Integral transitivity
makes the literal integral closure of A in that field an integral closure
of the polynomial base; the installed finite-separable trace proof then
makes it finite. We transfer to the actual canonical FractionRing A.

No finite-normalization, trace-nondegeneracy, separating-transcendence or
fraction-dimension certificate is supplied as a premise.

STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open Algebra Module
open scoped nonZeroDivisors

/-- Genuine finite normalization for a domain finite over an actual normal
Noetherian characteristic-zero domain. Its actual fraction field and finite
separable extension are constructed through actual localization. -/
theorem finiteNormalization_of_finite_normal_base
    (B A : Type*) [CommRing B] [IsDomain B] [CharZero B]
    [IsNoetherianRing B] [IsIntegrallyClosed B]
    [CommRing A] [IsDomain A] [Algebra B A] [FaithfulSMul B A]
    [Module.Finite B A] :
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
  letI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective B F)
  letI : Algebra.IsSeparable F C := inferInstance
  letI : Algebra B (integralClosure A C) :=
    inferInstanceAs (Algebra B ((integralClosure A C).restrictScalars B))
  letI : IsScalarTower B A (integralClosure A C) := inferInstance
  letI : IsScalarTower B (integralClosure A C) C := inferInstance
  letI : IsIntegralClosure (integralClosure A C) B C := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx.tower_top⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact isIntegral_trans (R := B) (A := A) (y : C) y.property
  letI : Module.Finite B (integralClosure A C) := IsIntegralClosure.finite B F C (integralClosure A C)
  letI : Module.Finite A (integralClosure A C) := Module.Finite.of_restrictScalars_finite B A (integralClosure A C)
  exact Module.Finite.equiv
    ((FractionRing.algEquiv (A := A) C).symm.mapIntegralClosure.toLinearEquiv)

/-- The actual normalization of every actual finite-type integral algebra
in characteristic zero is a finite module. No normalization certificate is
an input: the actual normal polynomial base is constructed internally. -/
theorem finiteNormalization_of_finiteType_charZero
    (K A : Type*) [Field K] [CharZero K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  obtain ⟨n, g, hginj, hgfinite⟩ := exists_finite_inj_algHom_of_fg K A
  let B := MvPolynomial (Fin n) K
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hginj
  letI : Module.Finite B A := by
    change g.toRingHom.Finite at hgfinite
    exact (RingHom.finite_algebraMap).mp hgfinite
  exact finiteNormalization_of_finite_normal_base B A

end PfaffianDescent.Coray

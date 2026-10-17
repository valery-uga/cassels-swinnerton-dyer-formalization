import PfaffianDescent.ActualSeparableBaseChangeStalkParameter198
import Mathlib.RingTheory.Flat.TorsionFree

/-! Flat stalk maps preserve the actual original regular parameter. Together
with198 this constructs both regularity and maximal-ideal generation after
finite separable base change, without a target regularity premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped nonZeroDivisors
universe u v

theorem flatRingHom_parameter_regular204
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (phi : R →+* S) (hphi : phi.Flat) (t : R) (ht : t ∈ R⁰) :
    phi t ∈ S⁰ := by
  letI : Algebra R S := phi.toAlgebra
  letI : Module.Flat R S := hphi
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S) ht
  simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_zero] using hx

theorem actualFlatStalk_parameter_regular204
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X)
    (t : Y.presheaf.stalk (f x)) (ht : t ∈ (Y.presheaf.stalk (f x))⁰) :
    (f.stalkMap x).hom t ∈ (X.presheaf.stalk x)⁰ :=
  flatRingHom_parameter_regular204 (f.stalkMap x).hom (Flat.stalkMap f x) t ht

theorem actualFiniteSeparableBaseChangeStalk_regularParameter204
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (x : schemeBaseChangeToField (L := L) X p)
    (t : X.presheaf.stalk (cubicPointTraceFieldBaseChangeProjection K L p x))
    (ht : t ∈ (X.presheaf.stalk
      (cubicPointTraceFieldBaseChangeProjection K L p x))⁰)
    (hspan : maximalIdeal
      (X.presheaf.stalk (cubicPointTraceFieldBaseChangeProjection K L p x)) =
      Ideal.span ({t} : Set
        (X.presheaf.stalk (cubicPointTraceFieldBaseChangeProjection K L p x)))) :
    let t' := ((cubicPointTraceFieldBaseChangeProjection K L p).stalkMap x).hom t
    t' ∈ ((schemeBaseChangeToField (L := L) X p).presheaf.stalk x)⁰ ∧
      maximalIdeal ((schemeBaseChangeToField (L := L) X p).presheaf.stalk x) =
        Ideal.span ({t'} : Set ((schemeBaseChangeToField (L := L) X p).presheaf.stalk x)) := by
  letI : Etale (cubicPointTraceFieldBaseChangeProjection K L p) :=
    actualFiniteSeparableBaseChangeProjection_etale198 K L p
  exact ⟨actualFlatStalk_parameter_regular204
      (cubicPointTraceFieldBaseChangeProjection K L p) x t ht,
    actualFiniteSeparableBaseChangeStalk_parameter198 K L p x t hspan⟩

end PfaffianDescent

import PfaffianDescent.PointCartierNativeStalkPrincipalNormalization
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! Ring-equivalence transport of the whole principal extension, including
its actual quotient projection. No quotient-comparison square is assumed. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
universe u w w'
set_option backward.isDefEq.respectTransparency false

lemma ringEquiv_symm_parameter_regular199
    {C B : Type u} [CommRing C] [CommRing B]
    (e : C ≃+* B) (t : B) (ht : t ∈ B⁰) : e.symm t ∈ C⁰ := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  apply e.injective
  have h : t * e x = 0 := by
    simpa only [map_mul, e.apply_symm_apply, map_zero] using congrArg e hx
  exact (mem_nonZeroDivisors_iff_left.mp ht (e x) h).trans (map_zero e).symm

lemma principalRingEquiv_first_square199
    {C B : Type u} [CommRing C] [CommRing B]
    (e : C ≃+* B) (t : B) :
    ((pointCartierYonedaCoefficientComplex t).map
      (ModuleCat.restrictScalars e.toRingHom)).f ≫
        (ModuleCat.restrictScalarsIsoOfEquiv e).hom =
      (ModuleCat.restrictScalarsIsoOfEquiv e).hom ≫
        (pointCartierYonedaCoefficientComplex (e.symm t)).f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change B at x
  change e.symm (t * x) = e.symm t * e.symm x
  exact map_mul e.symm t x

/-- The third component is constructed by the native cokernel universal
property, so the whole quotient and its literal projection are retained. -/
def principalRingEquivWholeSequenceIso199
    {C B : Type u} [CommRing C] [CommRing B]
    (e : C ≃+* B) (t : B) (ht : t ∈ B⁰) :
    (pointCartierYonedaCoefficientComplex t).map
        (ModuleCat.restrictScalars e.toRingHom) ≅
      pointCartierYonedaCoefficientComplex (e.symm t) := by
  let V := (pointCartierYonedaCoefficientComplex t).map
    (ModuleCat.restrictScalars e.toRingHom)
  let T := pointCartierYonedaCoefficientComplex (e.symm t)
  let hV : V.ShortExact :=
    (pointCartierYonedaCoefficientComplex_shortExact t ht).map_of_exact _
  let hT : T.ShortExact := pointCartierYonedaCoefficientComplex_shortExact _
    (ringEquiv_symm_parameter_regular199 e t ht)
  let a := ModuleCat.restrictScalarsIsoOfEquiv e
  let hc := principalRingEquiv_first_square199 e t
  exact ShortComplex.isoMk a a
    (pointCartierNativeStalkCokernelIso V T hV hT a a hc)
    hc.symm
    (pointCartierNativeStalkCokernelIso_square V T hV hT a a hc).symm

lemma principalRingEquivWholeSequenceIso_projection199
    {C B : Type u} [CommRing C] [CommRing B]
    (e : C ≃+* B) (t : B) (ht : t ∈ B⁰) :
    ((pointCartierYonedaCoefficientComplex t).map
      (ModuleCat.restrictScalars e.toRingHom)).g ≫
        (principalRingEquivWholeSequenceIso199 e t ht).hom.τ₃ =
      (ModuleCat.restrictScalarsIsoOfEquiv e).hom ≫
        (pointCartierYonedaCoefficientComplex (e.symm t)).g :=
  (principalRingEquivWholeSequenceIso199 e t ht).hom.comm₂₃.symm

/-- A literal point parameter in the original maximal ideal makes the
lifted two-generator surface ideal proper; no nonvanishing premise is used. -/
lemma principalRingEquiv_lift_pair_one_not_mem_span199
    {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing B]
    (f g : R) (e : (R ⧸ Ideal.span {f}) ≃+* B)
    (hmem : e (Ideal.Quotient.mk (Ideal.span {f}) g) ∈ IsLocalRing.maximalIdeal B) :
    (1 : R) ∉ Ideal.span ({f, g} : Set R) := by
  intro hone
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hone
  let q := Ideal.Quotient.mk (Ideal.span {f})
  have hrf : IsLocalRing.residue B (e (q f)) = 0 := by
    rw [Ideal.Quotient.mk_singleton_self, map_zero, map_zero]
  have hrg : IsLocalRing.residue B (e (q g)) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  have h := congrArg (fun r => IsLocalRing.residue B (e (q r))) hab
  have hz : (0 : IsLocalRing.ResidueField B) = 1 := by
    simpa only [map_add, map_mul, map_one, hrf, hrg, mul_zero, zero_add] using h
  exact zero_ne_one hz

end PfaffianDescent

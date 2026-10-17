import PfaffianDescent.PointCartierNativeStalkRestrictionExtInjective
import PfaffianDescent.PointCartierNativeStalkExtFunctorNaturality
import PfaffianDescent.ExtMapFixedSource
import PfaffianDescent.PointCartierNativeStalkAmbientExtTwo
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-! # Nonzero classes survive restriction through the actual Cartier quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u w w' w''

def pointCartierNativeStalkQuotientPairIso
    {C B : Type u} [CommRing C] [CommRing B] (e : C ≃+* B) (g h : C) :
    (ModuleCat.restrictScalars e.toRingHom).obj
      (ModuleCat.of B (B ⧸ Ideal.span ({e g, e h} : Set B))) ≅
        ModuleCat.of C (C ⧸ Ideal.span ({g, h} : Set C)) := by
  let er := Ideal.quotientEquiv (Ideal.span ({g, h} : Set C))
    (Ideal.span ({e g, e h} : Set B)) e (by
      simp only [Ideal.map_span, Set.image_pair]
      rfl)
  letI : Module C (ModuleCat.of B (B ⧸ Ideal.span ({e g, e h} : Set B))) :=
    Module.compHom _ e.toRingHom
  exact LinearEquiv.toModuleIso
    { __ := er.symm
      map_smul' r x := by
        change er.symm (Ideal.Quotient.mk (Ideal.span ({e g, e h} : Set B)) (e r) * x) =
          Ideal.Quotient.mk (Ideal.span ({g, h} : Set C)) r * er.symm x
        rw [map_mul, Ideal.quotientEquiv_symm_mk, e.symm_apply_apply] }

theorem pointCartierNativeStalkActualRestriction_eq_zero_iff
    {R B : Type u} [CommRing R] [CommRing B]
    [hExtR : HasExt.{w} (ModuleCat R)]
    (t g h : R) [hExtC : HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {t}))]
    [hExtB : HasExt.{w''} (ModuleCat B)]
    (e : (R ⧸ Ideal.span {t}) ≃+* B)
    (φ : R →+* B) (hφ : φ = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t})))
    (ht : t ∈ R⁰)
    (hg : e (Ideal.Quotient.mk (Ideal.span {t}) g) ∈ B⁰)
    (hh : Ideal.Quotient.mk
      (Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)})
      (e (Ideal.Quotient.mk (Ideal.span {t}) h)) ∈
        (B ⧸ Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)})⁰)
    (z : Ext.{w''}
      (ModuleCat.of B (B ⧸ Ideal.span
        ({e (Ideal.Quotient.mk (Ideal.span {t}) g),
          e (Ideal.Quotient.mk (Ideal.span {t}) h)} : Set B)))
      (ModuleCat.of B B) 2) :
    z.mapExactFunctor (ModuleCat.restrictScalars φ) = 0 ↔ z = 0 := by
  constructor
  · intro hz
    let q := Ideal.Quotient.mk (Ideal.span {t})
    let E := ModuleCat.restrictScalars e.toRingHom
    let Q := ModuleCat.restrictScalars q
    let F := ModuleCat.restrictScalars φ
    let η := ModuleCat.restrictScalarsComp' q e.toRingHom φ hφ
    have hnat := pointCartierNativeStalkExtFunctorNaturality F (E ⋙ Q) η.hom z
    change (z.mapExactFunctor F).comp (Ext.mk₀ (η.app _).hom) (add_zero 2) =
      (Ext.mk₀ (η.app _).hom).comp (z.mapExactFunctor (E ⋙ Q)) (zero_add 2) at hnat
    rw [hz, Ext.zero_comp] at hnat
    have hcomp : z.mapExactFunctor (E ⋙ Q) = 0 := by
      have heq := congrArg
        (fun a ↦ (Ext.mk₀ (η.app _).inv).comp a (zero_add 2)) hnat
      simpa only [Ext.comp_zero, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id,
        Ext.mk₀_id_comp] using heq.symm
    rw [← pointCartierNativeStalkExtFunctorComposition E Q z] at hcomp
    let eM := pointCartierNativeStalkQuotientPairIso e (q g) (q h)
    let eN := ModuleCat.restrictScalarsIsoOfEquiv e
    let zC := extPostcompIsoOfIso eN ((extPrecompIsoOfIso eM) (z.mapExactFunctor E))
    have hzC : zC.mapExactFunctor Q = 0 := by
      change (((Ext.mk₀ eM.inv).comp (z.mapExactFunctor E) (zero_add 2)).comp
        (Ext.mk₀ eN.hom) (add_zero 2)).mapExactFunctor Q = 0
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, hcomp,
        Ext.comp_zero, Ext.zero_comp]
    have hzC0 : zC = 0 :=
      (pointCartierNativeStalkRestrictionExtTwo_eq_zero_iff t g h ht
        (pointCartierNativeStalkRegularLift_first t g e hg)
        (pointCartierNativeStalkRegularLift_second t g h e hh) zC).mp hzC
    have hzE : z.mapExactFunctor E = 0 := by
      apply (extPrecompIsoOfIso eM).injective
      apply (extPostcompIsoOfIso eN).injective
      simpa only [map_zero] using hzC0
    apply (E.mapExt_bijective_of_preservesInjectiveObjects _ _ 2).injective
    change z.mapExactFunctor E = (0 : Ext.{w''} _ _ 2).mapExactFunctor E
    simpa only [Ext.mapExactFunctor_zero] using hzE
  · rintro rfl
    simp only [Ext.mapExactFunctor_zero]

theorem pointCartierNativeStalkActualRestrictionEndpoints_eq_zero_iff
    {R B : Type u} [CommRing R] [CommRing B]
    [hExtR : HasExt.{w} (ModuleCat R)]
    (t g h : R) [hExtC : HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {t}))]
    [hExtB : HasExt.{w''} (ModuleCat B)]
    (e : (R ⧸ Ideal.span {t}) ≃+* B)
    (φ : R →+* B) (hφ : φ = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t})))
    (ht : t ∈ R⁰)
    (hg : e (Ideal.Quotient.mk (Ideal.span {t}) g) ∈ B⁰)
    (hh : Ideal.Quotient.mk
      (Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)})
      (e (Ideal.Quotient.mk (Ideal.span {t}) h)) ∈
        (B ⧸ Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)})⁰)
    (M N : ModuleCat B)
    (qM : M ≅ ModuleCat.of B (B ⧸ Ideal.span
      ({e (Ideal.Quotient.mk (Ideal.span {t}) g),
        e (Ideal.Quotient.mk (Ideal.span {t}) h)} : Set B)))
    (qN : N ≅ ModuleCat.of B B) (z : Ext.{w''} M N 2) :
    z.mapExactFunctor (ModuleCat.restrictScalars φ) = 0 ↔ z = 0 := by
  constructor
  · intro hz
    let z' := extPostcompIsoOfIso qN ((extPrecompIsoOfIso qM) z)
    have hz' : z'.mapExactFunctor (ModuleCat.restrictScalars φ) = 0 := by
      change (((Ext.mk₀ qM.inv).comp z (zero_add 2)).comp
        (Ext.mk₀ qN.hom) (add_zero 2)).mapExactFunctor _ = 0
      rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, hz,
        Ext.comp_zero, Ext.zero_comp]
    have hz'0 := (pointCartierNativeStalkActualRestriction_eq_zero_iff
      t g h e φ hφ ht hg hh z').mp hz'
    apply (extPrecompIsoOfIso qM).injective
    apply (extPostcompIsoOfIso qN).injective
    simpa only [map_zero] using hz'0
  · rintro rfl
    simp only [Ext.mapExactFunctor_zero]

def pointCartierNativeStalkActualAmbientPointIso
    {R B : Type u} [CommRing R] [CommRing B]
    (t g h : R) (e : (R ⧸ Ideal.span {t}) ≃+* B)
    (φ : R →+* B) (hφ : φ = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t})))
    (ht : t ∈ R⁰)
    (hg : e (Ideal.Quotient.mk (Ideal.span {t}) g) ∈ B⁰)
    (hh : Ideal.Quotient.mk
      (Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)})
      (e (Ideal.Quotient.mk (Ideal.span {t}) h)) ∈
        (B ⧸ Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)})⁰)
    (M : ModuleCat B)
    (qM : M ≅ ModuleCat.of B (B ⧸ Ideal.span
      ({e (Ideal.Quotient.mk (Ideal.span {t}) g),
        e (Ideal.Quotient.mk (Ideal.span {t}) h)} : Set B))) :
    (ModuleCat.restrictScalars φ).obj M ≅ pointCartierYonedaAmbientPoint t g h := by
  let q := Ideal.Quotient.mk (Ideal.span {t})
  let E := ModuleCat.restrictScalars e.toRingHom
  let Q := ModuleCat.restrictScalars q
  let hgC := pointCartierNativeStalkRegularLift_first t g e hg
  let hhC := pointCartierNativeStalkRegularLift_second t g h e hh
  let ha := pointCartierNativeStalkRegularLift_third t g h hhC
  let heq : t = t * ((1 : Rˣ) : R) + g * 0 + h * 0 := by simp
  let κ := pointCartierYonedaSourceComparison t g h t 1 0 0 heq ht hgC ha hgC hhC
  letI : IsIso κ.onP := pointCartierYonedaSourceComparison_onP_isIso
    t g h t 1 0 0 heq ht hgC ha hgC hhC
  exact (ModuleCat.restrictScalarsComp' q e.toRingHom φ hφ).app M ≪≫
    Q.mapIso (E.mapIso qM ≪≫ pointCartierNativeStalkQuotientPairIso e (q g) (q h)) ≪≫
      (asIso κ.onP).symm

theorem pointCartierNativeStalkActualAmbientExtTwo_subsingleton
    {R B : Type u} [CommRing R] [CommRing B]
    [hExtR : HasExt.{w} (ModuleCat R)]
    (t g h : R) (e : (R ⧸ Ideal.span {t}) ≃+* B)
    (φ : R →+* B) (hφ : φ = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t})))
    (ht : t ∈ R⁰)
    (hg : e (Ideal.Quotient.mk (Ideal.span {t}) g) ∈ B⁰)
    (hh : Ideal.Quotient.mk
      (Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)})
      (e (Ideal.Quotient.mk (Ideal.span {t}) h)) ∈
        (B ⧸ Ideal.span {e (Ideal.Quotient.mk (Ideal.span {t}) g)})⁰)
    (M : ModuleCat B)
    (qM : M ≅ ModuleCat.of B (B ⧸ Ideal.span
      ({e (Ideal.Quotient.mk (Ideal.span {t}) g),
        e (Ideal.Quotient.mk (Ideal.span {t}) h)} : Set B))) :
    Subsingleton (Ext.{w} ((ModuleCat.restrictScalars φ).obj M) (ModuleCat.of R R) 2) := by
  let hgC := pointCartierNativeStalkRegularLift_first t g e hg
  let hhC := pointCartierNativeStalkRegularLift_second t g h e hh
  let ha := pointCartierNativeStalkRegularLift_third t g h hhC
  letI : Subsingleton (Ext.{w} (pointCartierYonedaAmbientPoint t g h)
      (ModuleCat.of R R) 2) :=
    pointCartierNativeStalkAmbientExtTwo_subsingleton t g h ht hgC ha
  exact (extPrecompIsoOfIso
    (pointCartierNativeStalkActualAmbientPointIso t g h e φ hφ ht hg hh M qM)).toEquiv.subsingleton_congr.mpr
      inferInstance

end PfaffianDescent

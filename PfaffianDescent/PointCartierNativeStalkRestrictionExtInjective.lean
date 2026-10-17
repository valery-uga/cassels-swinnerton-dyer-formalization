import PfaffianDescent.PointCartierNativeStalkRegularLifts

/-! # Restriction of scalars does not kill the surface point Ext class -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u w w'
variable {R : Type u} [CommRing R]

theorem pointCartierNativeStalkSurfaceClass_postcomp
    [hExt : HasExt.{w} (ModuleCat R)] (g h r : R) (hg : g ∈ R⁰)
    (hh : Ideal.Quotient.mk (Ideal.span {g}) h ∈ (R ⧸ Ideal.span {g})⁰) :
    (localSerreExtTwoClass g h 1 hg hh).comp
      (Ext.mk₀ (ModuleCat.ofHom (LinearMap.lsmul R R r))) (add_zero 2) =
        localSerreExtTwoClass g h r hg hh := by
  have hs : ModuleCat.ofHom (LinearMap.lsmul R R r) = r • 𝟙 (ModuleCat.of R R) := by
    ext x
    rfl
  rw [hs, ← Ext.smul_eq_comp_mk₀,
    ← localExtTwoCoefficientMap_apply_eq_localSerreExtTwoClass,
    ← localExtTwoCoefficientMap_apply_eq_localSerreExtTwoClass]
  simpa only [smul_eq_mul, mul_one] using
    ((localExtTwoCoefficientMap g h hg hh).map_smul r 1).symm

theorem pointCartierNativeStalkAmbientClass_postcomp
    [hExt : HasExt.{w} (ModuleCat R)]
    (f g h : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) (r : R) :
    (pointCartierYonedaAmbientClass f g h hf hg hh 1).comp
      (Ext.mk₀ (ModuleCat.ofHom (LinearMap.lsmul R R r))) (add_zero 3) =
        pointCartierYonedaAmbientClass f g h hf hg hh r := by
  have hc : DegreeThreeCocycle.postcompAddHom (0 : ModuleCat.of R PUnit ⟶ ModuleCat.of R R)
      (ModuleCat.ofHom (LinearMap.lsmul R R r)) (pointCartierYonedaAmbientTopCocycle 1) =
        pointCartierYonedaAmbientTopCocycle r := by
    apply Subtype.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change r * (1 * x) = r * x
    rw [one_mul]
  unfold pointCartierYonedaAmbientClass
  rw [ThreeStepResolution.connecting_postcomp, ← degreeThreeCocycleDesc_postcomp, hc]

def pointCartierNativeStalkCoefficientScalarHom (p r : R) :
    pointCartierYonedaCoefficientComplex p ⟶ pointCartierYonedaCoefficientComplex p where
  τ₁ := ModuleCat.ofHom (LinearMap.lsmul R R r)
  τ₂ := ModuleCat.ofHom (LinearMap.lsmul R R r)
  τ₃ := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {p}))).map
    (ModuleCat.ofHom (LinearMap.lsmul (R ⧸ Ideal.span {p}) (R ⧸ Ideal.span {p})
      (Ideal.Quotient.mk (Ideal.span {p}) r)))
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change R at x
    change p * (r * x) = r * (p * x)
    ring
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change R at x
    change Ideal.Quotient.mk (Ideal.span {p}) (r * x) =
      Ideal.Quotient.mk (Ideal.span {p}) r * Ideal.Quotient.mk (Ideal.span {p}) x
    exact map_mul _ _ _

theorem pointCartierNativeStalkSurfaceBoundary_coefficient
    [hExt : HasExt.{w} (ModuleCat R)]
    (t g h : R) [hExtB : HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {t}))]
    (ht : t ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {t}) g ∈ (R ⧸ Ideal.span {t})⁰)
    (hh : Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) g})
      (Ideal.Quotient.mk (Ideal.span {t}) h) ∈
        ((R ⧸ Ideal.span {t}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) g})⁰)
    (r : R) :
    let ha := pointCartierNativeStalkRegularLift_third t g h hh
    let heq : t = t * ((1 : Rˣ) : R) + g * 0 + h * 0 := by simp
    let φ := pointCartierYonedaSourceComparison t g h t 1 0 0 heq ht hg ha hg hh
    ((Ext.mk₀ φ.onP).comp
      ((localSerreExtTwoClass (Ideal.Quotient.mk (Ideal.span {t}) g)
        (Ideal.Quotient.mk (Ideal.span {t}) h) (Ideal.Quotient.mk (Ideal.span {t}) r) hg hh).mapExactFunctor
          (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {t})))) (zero_add 2)).comp
      (pointCartierYonedaCoefficientComplex_shortExact t ht).extClass rfl =
        pointCartierYonedaAmbientClass t g h ht hg ha r := by
  dsimp only
  let q := Ideal.Quotient.mk (Ideal.span {t})
  let F := ModuleCat.restrictScalars q
  let ha := pointCartierNativeStalkRegularLift_third t g h hh
  let heq : t = t * ((1 : Rˣ) : R) + g * 0 + h * 0 := by simp
  let φ := pointCartierYonedaSourceComparison t g h t 1 0 0 heq ht hg ha hg hh
  let hs := pointCartierYonedaCoefficientComplex_shortExact t ht
  have hclass := (pointCartierNativeStalkSurfaceClass_postcomp
    (q g) (q h) (q r) hg hh).symm
  have hnat := hs.extClass_naturality hs (pointCartierNativeStalkCoefficientScalarHom t r)
  change hs.extClass.comp (Ext.mk₀ (ModuleCat.ofHom (LinearMap.lsmul R R r))) (add_zero 1) =
    (Ext.mk₀ (F.map (ModuleCat.ofHom
      (LinearMap.lsmul (R ⧸ Ideal.span {t}) (R ⧸ Ideal.span {t}) (q r))))).comp
      hs.extClass (zero_add 1) at hnat
  have hgen : ((Ext.mk₀ φ.onP).comp
      ((localSerreExtTwoClass (q g) (q h) 1 hg hh).mapExactFunctor F) (zero_add 2)).comp
        hs.extClass rfl = pointCartierYonedaAmbientClass t g h ht hg ha 1 := by
    simpa only [inv_one, Units.val_one] using
      (pointCartierYoneda_surface_generator_boundary t g h t (1 : Rˣ) 0 0 heq ht ht hg ha hg hh)
  rw [hclass, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero,
    ← hnat, ← Ext.comp_assoc_of_third_deg_zero, hgen,
    pointCartierNativeStalkAmbientClass_postcomp]

theorem pointCartierNativeStalkRestrictionExtTwo_eq_zero_iff
    [hExt : HasExt.{w} (ModuleCat R)]
    (t g h : R) [hExtB : HasExt.{w'} (ModuleCat (R ⧸ Ideal.span {t}))]
    (ht : t ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {t}) g ∈ (R ⧸ Ideal.span {t})⁰)
    (hh : Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) g})
      (Ideal.Quotient.mk (Ideal.span {t}) h) ∈
        ((R ⧸ Ideal.span {t}) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {t}) g})⁰)
    (z : Ext.{w'}
      (ModuleCat.of (R ⧸ Ideal.span {t}) ((R ⧸ Ideal.span {t}) ⧸
        Ideal.span ({Ideal.Quotient.mk (Ideal.span {t}) g,
          Ideal.Quotient.mk (Ideal.span {t}) h} : Set _)))
      (ModuleCat.of (R ⧸ Ideal.span {t}) (R ⧸ Ideal.span {t})) 2) :
    z.mapExactFunctor (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {t}))) = 0 ↔ z = 0 := by
  constructor
  · intro hz
    let q := Ideal.Quotient.mk (Ideal.span {t})
    let ha := pointCartierNativeStalkRegularLift_third t g h hh
    let heq : t = t * ((1 : Rˣ) : R) + g * 0 + h * 0 := by simp
    let φ := pointCartierYonedaSourceComparison t g h t 1 0 0 heq ht hg ha hg hh
    obtain ⟨b, hb⟩ := localExtTwoCoefficientMap_surjective (q g) (q h) hg hh z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hr : localSerreExtTwoClass (q g) (q h) (q r) hg hh = z :=
      (localExtTwoCoefficientMap_apply_eq_localSerreExtTwoClass (q g) (q h) (q r) hg hh).symm.trans hb
    have hbound := pointCartierNativeStalkSurfaceBoundary_coefficient t g h ht hg hh r
    dsimp only at hbound
    rw [hr, hz, Ext.comp_zero, Ext.zero_comp] at hbound
    have hmem := pointCartierYonedaAmbientClass_mem_of_eq_zero t g h ht hg ha r hbound.symm
    rw [← threeGeneratorLast_range] at hmem
    obtain ⟨⟨a, b, c⟩, habc⟩ := hmem
    have hq : q g * q b + q h * q c = q r := by
      have hqt : q t = 0 := Ideal.Quotient.mk_singleton_self t
      have he := congrArg q habc
      change q (t * a + g * b + h * c) = q r at he
      simpa only [map_add, map_mul, hqt,
        zero_mul, zero_add] using he
    have hmemB : q r ∈ Ideal.span ({q g, q h} : Set _) := by
      rw [← twoGeneratorLast_range]
      exact ⟨(q b, q c), hq⟩
    have hzero : localExtTwoCoefficientMap (q g) (q h) hg hh (q r) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [localExtTwoCoefficientMap_ker]
      exact hmemB
    rw [localExtTwoCoefficientMap_apply_eq_localSerreExtTwoClass, hr] at hzero
    exact hzero
  · rintro rfl
    simp only [Ext.mapExactFunctor_zero]

end PfaffianDescent

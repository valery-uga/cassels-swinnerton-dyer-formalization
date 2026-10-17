import PfaffianDescent.PointCartierYonedaAmbientNonzero
import PfaffianDescent.ResolutionCoefficientExtension

/-! # Degree-two ambient point Ext vanishes for a regular triple

Dual Koszul exactness is proved by an explicit matrix computation. The
principal Cartier boundary is consequently injective on every local class.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors

universe u w
variable {R : Type u} [CommRing R]

theorem pointCartierNativeStalkKoszulDual_exact
    (f g h : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R))
    (l : (R × R × R) →ₗ[R] R)
    (hl : l.comp (threeGeneratorFirst f g h) = 0) :
    ∃ q : (R × R × R) →ₗ[R] R, q.comp (threeGeneratorMiddle f g h) = l := by
  let a := l (1, 0, 0)
  let b := l (0, 1, 0)
  let c := l (0, 0, 1)
  have hrow (x : R × R × R) : l x = x.1 * a + x.2.1 * b + x.2.2 * c := by
    have hx : x = x.1 • (1, 0, 0) + x.2.1 • (0, 1, 0) + x.2.2 • (0, 0, 1) := by
      ext <;> simp
    conv_lhs => rw [hx]
    rw [map_add, map_add, map_smul, map_smul, map_smul]
    rfl
  have hzero := LinearMap.congr_fun hl 1
  simp only [LinearMap.comp_apply, threeGeneratorFirst, LinearMap.coe_mk,
    AddHom.coe_mk, mul_one, LinearMap.zero_apply] at hzero
  change l (h, -g, f) = 0 at hzero
  rw [hrow] at hzero
  have hz : (c, -b, a) ∈ LinearMap.ker (threeGeneratorLast f g h) := by
    change f * c + g * -b + h * a = 0
    linear_combination hzero
  rw [← pointCartierYoneda_last_exact hf hg hh] at hz
  obtain ⟨⟨s, t, u⟩, hstu⟩ := hz
  have hc : -g * s - h * t = c := congrArg Prod.fst hstu
  have hb : f * s - h * u = -b := congrArg (fun x : R × R × R ↦ x.2.1) hstu
  have ha : f * t + g * u = a := congrArg (fun x : R × R × R ↦ x.2.2) hstu
  let q : (R × R × R) →ₗ[R] R :=
    { toFun := fun x ↦ -u * x.1 + t * x.2.1 - s * x.2.2
      map_add' := by intro x y; change _ = _; simp only [Prod.fst_add, Prod.snd_add]; ring
      map_smul' := by intro r x; change _ = _; simp only [Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, RingHom.id_apply]; ring }
  refine ⟨q, ?_⟩
  apply LinearMap.ext
  rintro ⟨x, y, z⟩
  rw [LinearMap.comp_apply, hrow]
  change -u * (-g * x - h * y) + t * (f * x - h * z) - s * (f * y + g * z) =
    x * a + y * b + z * c
  linear_combination x * ha - y * hb + z * hc

theorem pointCartierNativeStalkAmbientExtTwo_subsingleton
    [hExt : HasExt.{w} (ModuleCat R)]
    (f g h : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) :
    Subsingleton (Ext.{w} (pointCartierYonedaAmbientPoint f g h) (ModuleCat.of R R) 2) := by
  let T := (pointCartierYonedaAmbientResolution f g h hf hg hh).toTwoStep
  letI : Subsingleton (Ext.{w} T.C₀ (ModuleCat.of R R) 2) := by
    change Subsingleton (Ext.{w} (ModuleCat.of R R) (ModuleCat.of R R) (1 + 1))
    exact Ext.subsingleton_of_projective _ _ 1
  letI : Subsingleton (Ext.{w} T.C₀ (ModuleCat.of R R) 1) := by
    change Subsingleton (Ext.{w} (ModuleCat.of R R) (ModuleCat.of R R) (0 + 1))
    exact Ext.subsingleton_of_projective _ _ 0
  letI : Subsingleton (Ext.{w} T.C₁ (ModuleCat.of R R) 1) := by
    change Subsingleton (Ext.{w} (ModuleCat.of R (R × R × R)) (ModuleCat.of R R) (0 + 1))
    exact Ext.subsingleton_of_projective _ _ 0
  suffices hz : ∀ z : Ext.{w} T.P (ModuleCat.of R R) 2, z = 0 by
    exact ⟨fun z z' ↦ (hz z).trans (hz z').symm⟩
  intro z
  obtain ⟨ψ, hψ⟩ := T.connecting_surjective (ModuleCat.of R R) z
  let l : ModuleCat.of R (R × R × R) ⟶ ModuleCat.of R R :=
    Abelian.coimage.π (ModuleCat.ofHom (threeGeneratorMiddle f g h)) ≫ ψ
  have hl : ModuleCat.ofHom (threeGeneratorFirst f g h) ≫ l = 0 := by
    dsimp only [l]
    rw [← Category.assoc, Abelian.comp_coimage_π_eq_zero
      (pointCartierYonedaAmbientMiddle_zero f g h), zero_comp]
  have hlin : l.hom.comp (threeGeneratorFirst f g h) = 0 :=
    congrArg ModuleCat.Hom.hom hl
  obtain ⟨q, hq⟩ := pointCartierNativeStalkKoszulDual_exact f g h hf hg hh l.hom hlin
  have hq' : ModuleCat.ofHom (threeGeneratorMiddle f g h) ≫ ModuleCat.ofHom q = l :=
    ModuleCat.hom_ext hq
  have hfactor : T.i₁ ≫ ModuleCat.ofHom q = ψ := by
    apply (cancel_epi (Abelian.coimage.π (ModuleCat.ofHom (threeGeneratorMiddle f g h)))).1
    change Abelian.coimage.π (ModuleCat.ofHom (threeGeneratorMiddle f g h)) ≫
      (Abelian.factorThruCoimage (ModuleCat.ofHom (threeGeneratorMiddle f g h)) ≫
        ModuleCat.ofHom q) = _
    rw [← Category.assoc, Abelian.coimage.fac]
    exact hq'
  rw [← hψ]
  exact (T.connecting_eq_zero_iff (ModuleCat.of R R) ψ).mpr ⟨ModuleCat.ofHom q, hfactor⟩

/-- Every nonzero degree-two ambient point class with principal-quotient
coefficients has nonzero actual Cartier Yoneda boundary. -/
theorem pointCartierNativeStalkPrincipalBoundary_eq_zero_iff
    [hExt : HasExt.{w} (ModuleCat R)]
    (f g h p : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) (hp : p ∈ R⁰)
    (z : Ext.{w} (pointCartierYonedaAmbientPoint f g h)
      (pointCartierYonedaCoefficientComplex p).X₃ 2) :
    z.comp (pointCartierYonedaCoefficientComplex_shortExact p hp).extClass rfl = 0 ↔ z = 0 := by
  constructor
  · intro hz
    letI : Subsingleton (Ext.{w} (pointCartierYonedaAmbientPoint f g h)
        (pointCartierYonedaCoefficientComplex p).X₂ 2) := by
      change Subsingleton (Ext.{w} (pointCartierYonedaAmbientPoint f g h) (ModuleCat.of R R) 2)
      exact pointCartierNativeStalkAmbientExtTwo_subsingleton f g h hf hg hh
    obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ _
      (pointCartierYonedaCoefficientComplex_shortExact p hp) z rfl hz
    have ha0 : a = 0 := Subsingleton.elim _ _
    rw [ha0, Ext.zero_comp] at ha
    exact ha.symm
  · rintro rfl
    simp only [Ext.zero_comp]

theorem pointCartierNativeStalkPrincipalBoundary_injective
    [hExt : HasExt.{w} (ModuleCat R)]
    (f g h p : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hh : ∀ x : R, h * x ∈ Ideal.span ({f, g} : Set R) →
      x ∈ Ideal.span ({f, g} : Set R)) (hp : p ∈ R⁰) :
    Function.Injective
      ((pointCartierYonedaCoefficientComplex_shortExact p hp).extClass.postcomp
        (pointCartierYonedaAmbientPoint f g h) (show 2 + 1 = 3 by rfl)) := by
  intro z z' hz
  apply sub_eq_zero.mp
  apply (pointCartierNativeStalkPrincipalBoundary_eq_zero_iff f g h p hf hg hh hp (z - z')).mp
  change ((pointCartierYonedaCoefficientComplex_shortExact p hp).extClass.postcomp
    (pointCartierYonedaAmbientPoint f g h) (show 2 + 1 = 3 by rfl)) (z - z') = 0
  rw [map_sub, hz, sub_self]

end PfaffianDescent

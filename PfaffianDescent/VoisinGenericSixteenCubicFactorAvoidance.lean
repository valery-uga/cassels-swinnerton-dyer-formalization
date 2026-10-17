import PfaffianDescent.VoisinGenericSixteenLowDegreeDetection
import AllCharacteristics.VoisinGenericCubicPoint
import PfaffianDescent.TopHomogeneousProduct
import PfaffianDescent.VoisinSectionChoice
import PfaffianDescent.VoisinGenericCubicSixteenSurjectivity

/-!
# Low-degree factors of a cubic through the generic sixteen points

The generic unordered finite scheme has a field as its coefficient algebra.
Injectivity of quadratic restriction on one normalized chart therefore
prevents any nonzero cubic vanishing there from having a linear factor.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Injectivity on homogeneous quadrics also detects homogeneous linear
forms, using the square of a linear form. -/
theorem linearRestriction_injective_of_quadraticRestriction_injective
    {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    [FiniteDimensional F A]
    (x : Fin 4 → A)
    (hquad : Function.Injective (homogeneousSectionRestriction
      (K := F) x 2)) :
    Function.Injective (homogeneousSectionRestriction (K := F) x 1) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro l hl
  let q : homogeneousSubmodule (Fin 4) F 2 :=
    ⟨l.val * l.val, by simpa using l.property.mul l.property⟩
  have hqev : homogeneousSectionRestriction (K := F) x 2 q = 0 := by
    change MvPolynomial.eval₂ (algebraMap F A) x (l.val * l.val) = 0
    rw [MvPolynomial.eval₂_mul]
    have hlev : MvPolynomial.eval₂ (algebraMap F A) x l.val = 0 := hl
    rw [hlev, zero_mul]
  have hqzero : q = 0 := hquad (by simpa using hqev)
  have hsq : l.val * l.val = 0 := congrArg Subtype.val hqzero
  have hlzero : l.val = 0 := (mul_eq_zero.mp hsq).elim id id
  exact Subtype.ext hlzero

/-- If quadratic restriction is injective into a domain, no product of a
nonzero linear form and a nonzero quadratic form can vanish on the finite
scheme. -/
theorem no_linear_quadratic_factor_of_quadraticRestriction_injective
    {F A : Type u} [Field F] [CommRing A] [IsDomain A] [Algebra F A]
    [FiniteDimensional F A]
    (x : Fin 4 → A)
    (hquad : Function.Injective (homogeneousSectionRestriction
      (K := F) x 2))
    (l : MvPolynomial (Fin 4) F) (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (q : MvPolynomial (Fin 4) F) (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0) :
    (l * q).eval₂ (algebraMap F A) x ≠ 0 := by
  intro hzero
  rw [MvPolynomial.eval₂_mul] at hzero
  rcases mul_eq_zero.mp hzero with hlval | hqval
  · have hlin := linearRestriction_injective_of_quadraticRestriction_injective x hquad
    have : (⟨l, hl⟩ : homogeneousSubmodule (Fin 4) F 1) = 0 :=
      hlin (by simpa [homogeneousSectionRestriction_apply] using hlval)
    exact hl0 (congrArg Subtype.val this)
  · have : (⟨q, hq⟩ : homogeneousSubmodule (Fin 4) F 2) = 0 :=
      hquad (by simpa [homogeneousSectionRestriction_apply] using hqval)
    exact hq0 (congrArg Subtype.val this)

/-- A nonzero homogeneous cubic vanishing on a finite scheme with field-like
coefficient algebra and injective quadratic restriction is irreducible in the
ambient four-variable polynomial ring. -/
theorem irreducible_cubic_of_quadraticRestriction_injective_on_domain
    {F A : Type u} [Field F] [CommRing A] [IsDomain A] [Algebra F A]
    [FiniteDimensional F A]
    (x : Fin 4 → A)
    (hquad : Function.Injective (homogeneousSectionRestriction
      (K := F) x 2))
    (q : MvPolynomial (Fin 4) F) (hq : q.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hqvan : q.eval₂ (algebraMap F A) x = 0) :
    Irreducible q := by
  rw [irreducible_iff]
  refine ⟨homogeneous_not_isUnit_of_pos_degree_of_eval_zero hq (by norm_num), ?_⟩
  intro a b hfactor
  by_contra hunit
  push Not at hunit
  have ha0 : a ≠ 0 := by
    intro ha
    apply hq0
    rw [hfactor, ha, zero_mul]
  have hb0 : b ≠ 0 := by
    intro hb
    apply hq0
    rw [hfactor, hb, mul_zero]
  obtain ⟨ha, hb⟩ :=
    homogeneous_factor_of_homogeneous_product ha0 hb0 (hfactor ▸ hq)
  have hapos : 0 < a.totalDegree := by
    by_contra hnot
    have hzero : a.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
    exact hunit.1 (isUnit_of_homogeneous_zero (hzero ▸ ha) ha0)
  have hbpos : 0 < b.totalDegree := by
    by_contra hnot
    have hzero : b.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
    exact hunit.2 (isUnit_of_homogeneous_zero (hzero ▸ hb) hb0)
  have hdegrees : a.totalDegree + b.totalDegree = 3 := by
    have hdeg : q.totalDegree = 3 := hq.totalDegree hq0
    rw [hfactor, MvPolynomial.totalDegree_mul_of_isDomain ha0 hb0] at hdeg
    exact hdeg
  rcases (by omega : a.totalDegree = 1 ∧ b.totalDegree = 2 ∨
      a.totalDegree = 2 ∧ b.totalDegree = 1) with hab | hba
  · have hnonzero := no_linear_quadratic_factor_of_quadraticRestriction_injective
      x hquad a (hab.1 ▸ ha) ha0 b (hab.2 ▸ hb) hb0
    exact hnonzero (by simpa only [← hfactor] using hqvan)
  · have hnonzero := no_linear_quadratic_factor_of_quadraticRestriction_injective
      x hquad b (hba.2 ▸ hb) hb0 a (hba.1 ▸ ha) ha0
    apply hnonzero
    rw [mul_comm, ← hfactor]
    exact hqvan

/-- The same normalized chart detects low-degree equations and rules out a
nontrivial ambient factorization of every cubic in its vanishing system. -/
structure GenericSixteenCubicIrreducibilityData
    (F A : Type u) [Field F] [CommRing A] [Algebra F A]
    (p : MvPolynomial (Fin 4) F) where
  x : Fin 4 → A
  surfaceZero : p.eval₂ (algebraMap F A) x = 0
  evalSurjective : Function.Surjective (eval₂Hom (algebraMap F A) x)
  quadraticRestrictionInjective : Function.Injective
    (homogeneousSectionRestriction (K := F) x 2)
  cubicIrreducible : ∀ q : MvPolynomial (Fin 4) F,
    q.IsHomogeneous 3 → q ≠ 0 →
      q.eval₂ (algebraMap F A) x = 0 → Irreducible q

/-- On the same chart, the first regular cubic chosen by the section
dimension argument is automatically irreducible in the ambient polynomial
ring. -/
theorem GenericSixteenCubicIrreducibilityData.exists_irreducibleRegularFirstCubic
    {F A : Type u} [Field F] [Infinite F] [CommRing A] [Algebra F A]
    [FiniteDimensional F A]
    {p : MvPolynomial (Fin 4) F}
    (D : GenericSixteenCubicIrreducibilityData F A p)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) F))).IsPrime)
    (hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank
      p hp D.x D.surfaceZero) :
    ∃ q : MvPolynomial (Fin 4) F,
      q.IsHomogeneous 3 ∧
      q.eval₂ (algebraMap F A) D.x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q ∧ Irreducible q := by
  obtain ⟨q, hqhom, hqzero, hq0, hrel⟩ :=
    exists_regular_cubic_section_data_of_prime_with_nonzero
      p hp hp0 D.x D.surfaceZero hsections hpprime
  exact ⟨q, hqhom, hqzero, hq0, hrel,
    D.cubicIrreducible q hqhom hq0 hqzero⟩

/-- For the actual generic rank-sixteen finite subscheme, every nonzero
homogeneous cubic vanishing on one normalized chart is irreducible as an
ambient four-variable polynomial. -/
theorem exists_cubicConfigurationGenericSixteen_irreducibleVanishingCubics
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 16).toScheme]
    [hordered : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left]
    [hbase : IsIntegral (cubicConfigurationBase p hp 16)]
    [Infinite (cubicConfigurationBase p hp 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 16 ≫
      cubicConfigurationToBase p hp 16)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 2) :
    let Q := cubicConfigurationBase p hp 16
    let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    Nonempty (GenericSixteenCubicIrreducibilityData
      Q.functionField Γ(D.val.subscheme, ⊤) (p.map a.hom)) := by
  dsimp only
  let Q := cubicConfigurationBase p hp 16
  let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  haveI : FiniteDimensional Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  letI : IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 16).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left
    exact hordered
  letI : IsField Γ(D.val.subscheme, ⊤) :=
    cubicConfigurationGenericFiniteSubscheme_isField p hp 16 a ha (0 : Fin 16)
  letI : Field Γ(D.val.subscheme, ⊤) :=
    (cubicConfigurationGenericFiniteSubscheme_isField
      p hp 16 a ha (0 : Fin 16)).toField
  obtain ⟨T⟩ := exists_cubicConfigurationGenericSixteen_lowDegreeRestriction_injective
    p hp hp0 hpprime a ha (d := 2) (by decide) (by decide) e
  exact ⟨{
    x := T.x
    surfaceZero := T.surfaceZero
    evalSurjective := T.evalSurjective
    quadraticRestrictionInjective := T.restrictionInjective
    cubicIrreducible := fun q hq hq0 hqvan =>
      irreducible_cubic_of_quadraticRestriction_injective_on_domain
        T.x T.restrictionInjective q hq hq0 hqvan
  }⟩

structure GenericSixteenIrreducibleRegularFirstCubicData
    (F A : Type u) [Field F] [CommRing A] [Algebra F A]
    (p : MvPolynomial (Fin 4) F) where
  detection : GenericSixteenCubicIrreducibilityData F A p
  q : MvPolynomial (Fin 4) F
  qHomogeneous : q.IsHomogeneous 3
  qZero : q.eval₂ (algebraMap F A) detection.x = 0
  qNonzero : q ≠ 0
  qRegular : IsRelPrime p q
  qIrreducible : Irreducible q

/-- The selected first cubic defines a prime hypersurface in ambient affine
four-space. This does not assert that its intersection with the original
cubic surface is integral. -/
theorem GenericSixteenIrreducibleRegularFirstCubicData.qPrincipalPrime
    {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    {p : MvPolynomial (Fin 4) F}
    (D : GenericSixteenIrreducibleRegularFirstCubicData F A p) :
    (Ideal.span ({D.q} : Set (MvPolynomial (Fin 4) F))).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime D.qIrreducible.prime

/-- The ambient coordinate ring cut out by the selected cubic is a domain. -/
theorem GenericSixteenIrreducibleRegularFirstCubicData.qQuotientIsDomain
    {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    {p : MvPolynomial (Fin 4) F}
    (D : GenericSixteenIrreducibleRegularFirstCubicData F A p) :
    IsDomain (MvPolynomial (Fin 4) F ⧸
      Ideal.span ({D.q} : Set (MvPolynomial (Fin 4) F))) := by
  letI : (Ideal.span ({D.q} : Set (MvPolynomial (Fin 4) F))).IsPrime :=
    D.qPrincipalPrime
  infer_instance

/-- The original surface equation is nonzero in the integral hypersurface
defined by the selected cubic. -/
theorem GenericSixteenIrreducibleRegularFirstCubicData.pNotMemQ
    {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    {p : MvPolynomial (Fin 4) F}
    (D : GenericSixteenIrreducibleRegularFirstCubicData F A p) :
    p ∉ Ideal.span ({D.q} : Set (MvPolynomial (Fin 4) F)) := by
  intro hp
  apply D.qIrreducible.not_isUnit
  obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton).mp hp
  exact D.qRegular.symm.isUnit_of_dvd ⟨c, hc⟩

/-- Equivalently, the surface cuts a non-zero-divisor on the integral ambient
cubic hypersurface selected through the generic sixteen points. -/
theorem GenericSixteenIrreducibleRegularFirstCubicData.pRegularModQ
    {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    {p : MvPolynomial (Fin 4) F}
    (D : GenericSixteenIrreducibleRegularFirstCubicData F A p) :
    ∀ y : MvPolynomial (Fin 4) F,
      p * y ∈ Ideal.span ({D.q} : Set (MvPolynomial (Fin 4) F)) →
        y ∈ Ideal.span ({D.q} : Set (MvPolynomial (Fin 4) F)) :=
  regular_mod_span_singleton_of_isRelPrime D.qRegular.symm

/-- The actual generic length-sixteen scheme has one chart on which the
first selected cubic is regular relative to the surface and irreducible as
an ambient polynomial. No extra section-count hypothesis is needed: it
follows from the rank-sixteen finite coefficient algebra. -/
theorem exists_cubicConfigurationGenericSixteen_irreducibleRegularFirstCubic
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase p hp)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 16).toScheme]
    [hordered : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left]
    [hbase : IsIntegral (cubicConfigurationBase p hp 16)]
    [Infinite (cubicConfigurationBase p hp 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 16 ≫
      cubicConfigurationToBase p hp 16)
    (hprime :
      (Ideal.span ({p.map a.hom} : Set
        (MvPolynomial (Fin 4)
          (cubicConfigurationBase p hp 16).functionField))).IsPrime)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 2) :
    let Q := cubicConfigurationBase p hp 16
    let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    Nonempty (GenericSixteenIrreducibleRegularFirstCubicData
      Q.functionField Γ(D.val.subscheme, ⊤) (p.map a.hom)) := by
  dsimp only
  let Q := cubicConfigurationBase p hp 16
  let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 16 a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  haveI : FiniteDimensional Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  obtain ⟨T⟩ := exists_cubicConfigurationGenericSixteen_irreducibleVanishingCubics
    p hp hp0 hpprime a ha e
  have hpη0 : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 16 a hp0
  have hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank
      (p.map a.hom) (hp.map a.hom) T.x T.surfaceZero :=
    cubic_degree_sixteen_vanishing_sections_finrank
      (p.map a.hom) (hp.map a.hom) hpη0 T.x T.surfaceZero
      (cubicConfigurationGenericSixteen_coefficientFinrank p hp a ha)
  obtain ⟨q, hqhom, hqzero, hq0, hqrel, hqirr⟩ :=
    T.exists_irreducibleRegularFirstCubic
      (hp.map a.hom) hpη0 hprime hsections
  exact ⟨{
    detection := T
    q := q
    qHomogeneous := hqhom
    qZero := hqzero
    qNonzero := hq0
    qRegular := hqrel
    qIrreducible := hqirr
  }⟩

end PfaffianDescent

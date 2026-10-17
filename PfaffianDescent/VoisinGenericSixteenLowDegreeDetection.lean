import PfaffianDescent.VoisinGenericSixteenLowDegreeAvoidance
import PfaffianDescent.HomogeneousFrameBaseChange

/-!
# Low-degree detection on the actual generic sixteen-point scheme

The ordered-lift incidence result is transported to the normalized chart of
the unordered generic finite subscheme. Its component evaluations detect all
coefficients of a ground-field homogeneous frame, also after scalar extension
to the configuration function field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

structure DetectingGenericSixteenHomogeneousFrame
    (F A L : Type u) [Field F] [CommRing A] [Field L]
    [Algebra F A] [Algebra F L]
    (p : MvPolynomial (Fin 4) F)
    {n : ℕ} (φ : Fin 16 → A →ₐ[F] L)
    (r : Fin n → MvPolynomial (Fin 4) F) where
  x : Fin 4 → A
  surfaceZero : p.eval₂ (algebraMap F A) x = 0
  evalSurjective : Function.Surjective (eval₂Hom (algebraMap F A) x)
  detects : ∀ c : Fin n → F,
    (∀ i, MvPolynomial.eval₂ (algebraMap F L)
      (fun j => φ i (x j))
      (∑ j, MvPolynomial.C (c j) * r j) = 0) → c = 0

/-- Coefficient detection makes evaluation injective on every homogeneous
space spanned by the detected frame. -/
theorem DetectingGenericSixteenHomogeneousFrame.restriction_injective_of_span_top
    {F A L : Type u} [Field F] [CommRing A] [Field L]
    [Algebra F A] [Algebra F L] [FiniteDimensional F A]
    {p : MvPolynomial (Fin 4) F} {n d : ℕ}
    {φ : Fin 16 → A →ₐ[F] L} {r : Fin n → MvPolynomial (Fin 4) F}
    (D : DetectingGenericSixteenHomogeneousFrame F A L p φ r)
    (hr : ∀ i, (r i).IsHomogeneous d)
    (hspan : Submodule.span F
      (Set.range (fun i => (⟨r i, hr i⟩ : homogeneousSubmodule (Fin 4) F d))) = ⊤) :
    Function.Injective (homogeneousSectionRestriction (K := F) D.x d) := by
  let v : Fin n → homogeneousSubmodule (Fin 4) F d :=
    fun i => ⟨r i, hr i⟩
  let ev := homogeneousSectionRestriction (K := F) D.x d
  have hLI : LinearIndependent F (fun i => ev (v i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum i
    have hc : c = 0 := D.detects c (by
      intro j
      have heval :
          MvPolynomial.eval₂ (algebraMap F A) D.x
            (∑ k, MvPolynomial.C (c k) * r k) =
          ∑ k, c k • ev (v k) := by
        simp [ev, v, homogeneousSectionRestriction_apply,
          MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, Algebra.smul_def]
      have hcomp := MvPolynomial.hom_eval₂
        (∑ k, MvPolynomial.C (c k) * r k)
        (algebraMap F A) (φ j).toRingHom D.x
      have hmap : (φ j).toRingHom.comp (algebraMap F A) =
          algebraMap F L := by
        ext t
        exact (φ j).commutes t
      rw [hmap] at hcomp
      have hj : MvPolynomial.eval₂ (algebraMap F L)
          (fun k => φ j (D.x k))
          (∑ k, MvPolynomial.C (c k) * r k) =
          φ j (MvPolynomial.eval₂ (algebraMap F A) D.x
            (∑ k, MvPolynomial.C (c k) * r k)) := by
        simpa using hcomp.symm
      rw [hj, heval, hsum, map_zero])
    simpa [hc]
  have hdisj : Disjoint (Submodule.span F (Set.range v))
      (LinearMap.ker ev) := Submodule.range_ker_disjoint hLI
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  have hwspan : w ∈ Submodule.span F (Set.range v) := by
    rw [show Submodule.span F (Set.range v) = ⊤ from hspan]
    trivial
  exact (Submodule.mem_bot F).mp (hdisj.le_bot ⟨hwspan, hw⟩)

/-- Coefficient detection is sufficient for injectivity; the surface equation
and surjectivity data of a normalized chart are not needed for this step. -/
theorem homogeneousSectionRestriction_injective_of_component_detection
    {F A L : Type u} [Field F] [CommRing A] [Field L]
    [Algebra F A] [Algebra F L] [FiniteDimensional F A]
    {n d : ℕ} (x : Fin 4 → A)
    (φ : Fin 16 → A →ₐ[F] L)
    (r : Fin n → MvPolynomial (Fin 4) F)
    (hr : ∀ i, (r i).IsHomogeneous d)
    (hdetect : ∀ c : Fin n → F,
      (∀ i, MvPolynomial.eval₂ (algebraMap F L)
        (fun j => φ i (x j))
        (∑ j, MvPolynomial.C (c j) * r j) = 0) → c = 0)
    (hspan : Submodule.span F
      (Set.range (fun i => (⟨r i, hr i⟩ :
        homogeneousSubmodule (Fin 4) F d))) = ⊤) :
    Function.Injective (homogeneousSectionRestriction (K := F) x d) := by
  let v : Fin n → homogeneousSubmodule (Fin 4) F d :=
    fun i => ⟨r i, hr i⟩
  let ev := homogeneousSectionRestriction (K := F) x d
  have hLI : LinearIndependent F (fun i => ev (v i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum i
    have hc : c = 0 := hdetect c (by
      intro j
      have heval :
          MvPolynomial.eval₂ (algebraMap F A) x
            (∑ k, MvPolynomial.C (c k) * r k) =
          ∑ k, c k • ev (v k) := by
        simp [ev, v, homogeneousSectionRestriction_apply,
          MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, Algebra.smul_def]
      have hcomp := MvPolynomial.hom_eval₂
        (∑ k, MvPolynomial.C (c k) * r k)
        (algebraMap F A) (φ j).toRingHom x
      have hmap : (φ j).toRingHom.comp (algebraMap F A) =
          algebraMap F L := by
        ext t
        exact (φ j).commutes t
      rw [hmap] at hcomp
      have hj : MvPolynomial.eval₂ (algebraMap F L)
          (fun k => φ j (x k))
          (∑ k, MvPolynomial.C (c k) * r k) =
          φ j (MvPolynomial.eval₂ (algebraMap F A) x
            (∑ k, MvPolynomial.C (c k) * r k)) := by
        simpa using hcomp.symm
      rw [hj, heval, hsum, map_zero])
    simpa [hc]
  have hdisj : Disjoint (Submodule.span F (Set.range v))
      (LinearMap.ker ev) := Submodule.range_ker_disjoint hLI
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  have hwspan : w ∈ Submodule.span F (Set.range v) := by
    rw [show Submodule.span F (Set.range v) = ⊤ from hspan]
    trivial
  exact (Submodule.mem_bot F).mp (hdisj.le_bot ⟨hwspan, hw⟩)

/-- Detection of an arbitrary homogeneous frame on the normalized chart of
the actual generic rank-sixteen finite scheme. -/
theorem exists_cubicConfigurationGenericSixteen_detectingHomogeneousFrame_of_noCommon
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    {d n m : ℕ} (e : Fin m ≃ Monomials (Fin 4) d)
    (frame : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hframe : LinearIndependent K frame)
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt
      cubic hcubic e frame hframe z) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    Nonempty (DetectingGenericSixteenHomogeneousFrame
      Q.functionField Γ(D.val.subscheme, ⊤) (O.residueField z)
      (cubic.map a.hom) φ (fun j => (frame j).1.map a.hom)) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p' hp') := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  obtain ⟨ell, hell, x, he, hellOne, hxsurj, hpx, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_ambient_chart p' hp' D.val.subschemeι
  refine ⟨{
    x := x
    surfaceZero := hpx
    evalSurjective := hxsurj
    detects := ?_ }⟩
  exact cubicSixteenOrderedLift_normalizedAmbientChart_detectsFrame
    cubic hcubic a ha z hz e frame hframe hno
      ell hell x he hellOne hpoint

/-- The full linear or quadratic ground-field frame is detected on a
normalized chart of the actual generic sixteen-point finite subscheme. -/
theorem exists_cubicConfigurationGenericSixteen_detectingLowDegreeFrame
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime :
      (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {d m : ℕ} (hd : 0 < d) (hd3 : d < 3)
    (e : Fin m ≃ Monomials (Fin 4) d) :
    let W := homogeneousSubmodule (Fin 4) K d
    let frame := Module.finBasis K W
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    ∃ (z : O)
      (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField)),
      let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
      letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
      let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
        fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
          cubic hcubic a ha z hz i
      Nonempty (DetectingGenericSixteenHomogeneousFrame
        Q.functionField Γ(D.val.subscheme, ⊤) (O.residueField z)
        (cubic.map a.hom) φ (fun j => (frame j).1.map a.hom)) := by
  dsimp only
  obtain ⟨z, hz, hno⟩ :=
    exists_orderedPointOver_genericSixteen_with_noCommonLowDegreeEquation
      cubic hcubic hcubic_ne hcubic_prime hd hd3 e
  exact ⟨z, hz,
    exists_cubicConfigurationGenericSixteen_detectingHomogeneousFrame_of_noCommon
      cubic hcubic a ha z hz e
        (Module.finBasis K (homogeneousSubmodule (Fin 4) K d))
        (Module.finBasis K (homogeneousSubmodule (Fin 4) K d)).linearIndependent hno⟩

structure GenericSixteenLowDegreeRestrictionData
    (F A : Type u) [Field F] [CommRing A] [Algebra F A]
    (p : MvPolynomial (Fin 4) F) (d : ℕ) where
  x : Fin 4 → A
  surfaceZero : p.eval₂ (algebraMap F A) x = 0
  evalSurjective : Function.Surjective (eval₂Hom (algebraMap F A) x)
  restrictionInjective : Function.Injective
    (homogeneousSectionRestriction (K := F) x d)

/-- Every linear or quadratic form on the actual generic sixteen-point
scheme is detected by restriction in suitable normalized coordinates. In
particular there is no nonzero low-degree equation over the configuration
function field that vanishes on the entire finite subscheme. -/
theorem exists_cubicConfigurationGenericSixteen_lowDegreeRestriction_injective
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime :
      (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {d m : ℕ} (hd : 0 < d) (hd3 : d < 3)
    (e : Fin m ≃ Monomials (Fin 4) d) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    Nonempty (GenericSixteenLowDegreeRestrictionData
      Q.functionField Γ(D.val.subscheme, ⊤) (cubic.map a.hom) d) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  haveI : FiniteDimensional Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  letI : Algebra K Q.functionField := a.hom.toAlgebra
  let frame := Module.finBasis K (homogeneousSubmodule (Fin 4) K d)
  obtain ⟨z, hz, hdetect⟩ :=
    exists_cubicConfigurationGenericSixteen_detectingLowDegreeFrame
      cubic hcubic hcubic_ne hcubic_prime a ha hd hd3 e
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  obtain ⟨T⟩ := hdetect
  have hr : ∀ i, ((frame i).1.map a.hom).IsHomogeneous d := by
    intro i
    exact (frame i).property.map a.hom
  have hspan : Submodule.span Q.functionField
      (Set.range (fun i =>
        (⟨(frame i).1.map a.hom, hr i⟩ :
          homogeneousSubmodule (Fin 4) Q.functionField d))) = ⊤ := by
    have hbase := homogeneousFrame_baseChange_span_top
      (K := K) (L := Q.functionField) e frame
    rw [show algebraMap K Q.functionField = a.hom by rfl] at hbase
    have heq :
        (fun i => homogeneousSubmoduleBaseChange (σ := Fin 4) d a.hom
          (frame i)) =
        (fun i => (⟨(frame i).1.map a.hom, hr i⟩ :
          homogeneousSubmodule (Fin 4) Q.functionField d)) := by
      funext i
      apply Subtype.ext
      rfl
    rw [heq] at hbase
    exact hbase
  exact ⟨{
    x := T.x
    surfaceZero := T.surfaceZero
    evalSurjective := T.evalSurjective
    restrictionInjective := T.restriction_injective_of_span_top hr hspan
  }⟩


/-- The ordered-lift incidence hypothesis makes restriction injective on
any normalized ambient chart whose transported frame spans. -/
theorem cubicSixteenOrderedLift_normalizedAmbientChart_restriction_injective
    {K : Type u} [Field K]
    {d n m : ℕ}
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (e : Fin m ≃ Monomials (Fin 4) d)
    (frame : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hframe : LinearIndependent K frame)
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt cubic hcubic e frame hframe z) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    (hspan : Submodule.span Q.functionField
      (Set.range (fun i => homogeneousSubmoduleBaseChange (σ := Fin 4) d a.hom
        (frame i))) = ⊤) →
    ∀ (ell : MvPolynomial (Fin 4) Q.functionField)
      (hell : ell.IsHomogeneous 1)
      (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (he : ∀ q ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal,
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) q = 0)
      (hellOne : (Ideal.Quotient.lift
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) he)
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell) = 1),
      linearNormalizedPointAt
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField))
          x he
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell)
          (polynomial_class_mem_grading
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)) ell hell)
          hellOne ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField)) =
        D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient p' hp' →
      Function.Injective (homogeneousSectionRestriction (K := Q.functionField) x d) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  haveI : FiniteDimensional Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  letI : Algebra K Q.functionField := a.hom.toAlgebra
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
    fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
      cubic hcubic a ha z hz i
  intro hspan ell hell x he hellOne hpoint
  have hr : ∀ i, ((frame i).1.map a.hom).IsHomogeneous d := by
    intro i
    exact (frame i).property.map a.hom
  have hspan' : Submodule.span Q.functionField
      (Set.range (fun i =>
        (⟨(frame i).1.map a.hom, hr i⟩ :
          homogeneousSubmodule (Fin 4) Q.functionField d))) = ⊤ := by
    have heq :
        (fun i => homogeneousSubmoduleBaseChange (σ := Fin 4) d a.hom
          (frame i)) =
        (fun i => (⟨(frame i).1.map a.hom, hr i⟩ :
          homogeneousSubmodule (Fin 4) Q.functionField d)) := by
      funext i
      apply Subtype.ext
      rfl
    rw [heq] at hspan
    exact hspan
  have hdetect := cubicSixteenOrderedLift_normalizedAmbientChart_detectsFrame
    cubic hcubic a ha z hz e frame hframe hno ell hell x he hellOne hpoint
  exact homogeneousSectionRestriction_injective_of_component_detection
    x φ (fun j => (frame j).1.map a.hom) hr hdetect hspan'

end PfaffianDescent

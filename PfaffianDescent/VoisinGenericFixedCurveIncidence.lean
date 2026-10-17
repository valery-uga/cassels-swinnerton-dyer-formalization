import PfaffianDescent.VoisinGenericDegreeEightFixedCurveDichotomy
import PfaffianDescent.VoisinGenericQuadraticDetection

/-!
# Incidence supplied by the fixed-curve factor branch

This file identifies the normalized coordinates furnished by a factorization
of the generic length-eight scheme through a fixed curve with the eight
ordered residue-field points.  It is the coefficient-algebra bridge between
the fixed-curve dichotomy and the relative projective-family argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Normalized affine coordinates on a finite scheme, together with labeled
field evaluations that recover its marked ambient projective points and
annihilate one homogeneous equation. -/
structure OrderedNormalizedQuadraticIncidenceData
    {K Q A L : Type u} [Field K] [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    (a : K →+* Q) (q : MvPolynomial (Fin 4) Q)
    {X : Scheme.{u}} {n : ℕ}
    (r : Spec (.of L) ⟶ X)
    (marked : Fin n → (X ⟶ Proj (homogeneousSubmodule (Fin 4) K))) where
  ell : MvPolynomial (Fin 4) Q
  hell : ell.IsHomogeneous 1
  x : Fin 4 → A
  he : ∀ s ∈ (⊥ : HomogeneousIdeal
    (homogeneousSubmodule (Fin 4) Q)).toIdeal,
    (eval₂Hom (algebraMap Q A) x) s = 0
  hellOne : (Ideal.Quotient.lift
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)).toIdeal
    (eval₂Hom (algebraMap Q A) x) he)
      (Ideal.Quotient.mk
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q)).toIdeal ell) = 1
  φ : Fin n → A →ₐ[Q] L
  hzero : ∀ i, q.eval₂ (algebraMap Q L) (fun j => φ i (x j)) = 0
  hambient : ∀ i,
    Spec.map (CommRingCat.ofHom (φ i).toRingHom) ≫
        linearNormalizedPointAt
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
          x he
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q)).toIdeal ell)
          (polynomial_class_mem_grading
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
            ell hell) hellOne ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)) ≫
        ambientCoefficientMap a = r ≫ marked i

/-- Normalized incidence data place the underlying field point in the
universal finite-incidence bad locus for any family member represented by the
same equation. -/
theorem OrderedNormalizedQuadraticIncidenceData.mem_badLocus
    {K Q A L : Type u} [Field K] [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    (a : K →+* Q) (q : MvPolynomial (Fin 4) Q)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    {X T : Scheme.{u}} {n : ℕ}
    (xBase : X ⟶ Spec (.of K))
    (r : Spec (.of L) ⟶ X)
    (marked : Fin n → (X ⟶ Proj (homogeneousSubmodule (Fin 4) K)))
    (D : OrderedNormalizedQuadraticIncidenceData
      (A := A) (L := L) a q r marked)
    (t : Spec (.of L) ⟶ T)
    (tBase : T ⟶ Spec (.of K))
    (frame : T ⟶ projectiveParameters K (Fin 4) 2)
    (hbase : r ≫ xBase = t ≫ tBase)
    (hequation : Spec.map (CommRingCat.ofHom (algebraMap Q L)) ≫
      projectiveClassifyingMap q hq hq0 a = t ≫ frame) :
    r (IsLocalRing.closedPoint L) ∈
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) 2
        xBase tBase marked frame := by
  exact mem_projectiveUniversalFiniteIncidenceBadLocus_of_normalized_evaluation_zero
    a q hq hq0 D.x D.he D.ell D.hell D.hellOne
      xBase r marked t tBase frame hbase D.φ D.hzero D.hambient hequation

/-- A family member over the coefficient field may be pulled to the residue
field of the ordered configuration before applying the normalized incidence
criterion. -/
theorem OrderedNormalizedQuadraticIncidenceData.mem_badLocus_of_familyPoint
    {K Q A L : Type u} [Field K] [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    (a : K →+* Q) (b : Q →+* L)
    (hb : algebraMap Q L = b)
    (q : MvPolynomial (Fin 4) Q)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    {X T : Scheme.{u}} {n : ℕ}
    (xBase : X ⟶ Spec (.of K))
    (r : Spec (.of L) ⟶ X)
    (marked : Fin n → (X ⟶ Proj (homogeneousSubmodule (Fin 4) K)))
    (D : OrderedNormalizedQuadraticIncidenceData
      (A := A) (L := L) a q r marked)
    (t : Spec (.of Q) ⟶ T)
    (tBase : T ⟶ Spec (.of K))
    (frame : T ⟶ projectiveParameters K (Fin 4) 2)
    (hrbase : r ≫ xBase = Spec.map (CommRingCat.ofHom (b.comp a)))
    (htbase : t ≫ tBase = Spec.map (CommRingCat.ofHom a))
    (htframe : t ≫ frame = projectiveClassifyingMap q hq hq0 a) :
    r (IsLocalRing.closedPoint L) ∈
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) 2
        xBase tBase marked frame := by
  let tL : Spec (.of L) ⟶ T := Spec.map (CommRingCat.ofHom b) ≫ t
  have hbase : r ≫ xBase = tL ≫ tBase := by
    calc
      r ≫ xBase = Spec.map (CommRingCat.ofHom (b.comp a)) := hrbase
      _ = Spec.map (CommRingCat.ofHom b) ≫
          Spec.map (CommRingCat.ofHom a) := by
        rw [← Spec.map_comp]
        rfl
      _ = Spec.map (CommRingCat.ofHom b) ≫ (t ≫ tBase) := by rw [htbase]
      _ = tL ≫ tBase := by simp only [tL, Category.assoc]
  have hequation : Spec.map (CommRingCat.ofHom (algebraMap Q L)) ≫
      projectiveClassifyingMap q hq hq0 a = tL ≫ frame := by
    calc
      Spec.map (CommRingCat.ofHom (algebraMap Q L)) ≫
          projectiveClassifyingMap q hq hq0 a =
        Spec.map (CommRingCat.ofHom b) ≫
          projectiveClassifyingMap q hq hq0 a := by rw [hb]
      _ = Spec.map (CommRingCat.ofHom b) ≫ (t ≫ frame) := by rw [htframe]
      _ = tL ≫ frame := by simp only [tL, Category.assoc]
  exact D.mem_badLocus a q hq hq0 xBase r marked tL tBase frame
    hbase hequation

/-- If the coefficient-changed generic length-eight scheme factors through a
fixed curve, every quadratic equation of that curve vanishes at all eight
ordered residue-field points in one common normalized affine chart. -/
theorem exists_fixedCurve_factor_ordered_normalized_evaluations
    {K : Type u} [Field K] [CharZero K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    [Infinite (cubicConfigurationBase cubic hcubic 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
      cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 8).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 8 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 8 a ha).val.subschemeι)
    (q : MvPolynomial (Fin 4)
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (hq : q.IsHomogeneous 2) (hqC : q ∈ C.toIdeal) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsFinite
        (D.val.subschemeι ≫ hypersurfaceToBase
          (cubic.map a.hom) (hcubic.map a.hom)) := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI : IsFinite (h ≫ toBase C) :=
      (fixedCurve_factor_toBase (cubic.map a.hom) (hcubic.map a.hom)
        C hCp D.val.subschemeι h hfac).symm ▸ inferInstance
    letI := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    Nonempty (OrderedNormalizedQuadraticIncidenceData
      (A := Γ(D.val.subscheme, ⊤)) (L := O.residueField z) a.hom q
      (O.fromSpecResidueField z)
      (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 8
        (hypersurfaceToAmbient cubic hcubic) i)) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsFinite
      (D.val.subschemeι ≫ hypersurfaceToBase
        (cubic.map a.hom) (hcubic.map a.hom)) := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  let canonicalAlgebra := finiteSchemeCoefficientAlgebra pD
  let φRing : Fin 8 → Γ(D.val.subscheme, ⊤) →+* O.residueField z := fun i =>
    @AlgHom.toRingHom Q.functionField Γ(D.val.subscheme, ⊤) (O.residueField z)
      _ _ _ canonicalAlgebra _
      (quadraticOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i)
  have hφRing : ∀ i s,
      φRing i (@algebraMap Q.functionField Γ(D.val.subscheme, ⊤)
        _ _ canonicalAlgebra s) =
        algebraMap Q.functionField (O.residueField z) s := by
    intro i s
    exact @AlgHom.commutes Q.functionField Γ(D.val.subscheme, ⊤)
      (O.residueField z) _ _ _ canonicalAlgebra _
      (quadraticOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i) s
  have hfactorBase : h ≫ toBase C = pD :=
    fixedCurve_factor_toBase (cubic.map a.hom) (hcubic.map a.hom)
      C hCp D.val.subschemeι h hfac
  letI : IsFinite (h ≫ toBase C) := hfactorBase.symm ▸ inferInstance
  letI sourceAlgebra := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
  have hmap :
      (@algebraMap Q.functionField Γ(D.val.subscheme, ⊤)
        _ _ sourceAlgebra) =
      (@algebraMap Q.functionField Γ(D.val.subscheme, ⊤)
        _ _ canonicalAlgebra) :=
    finiteSchemeCoefficient_algebraMap_eq_of_eq (h ≫ toBase C) pD hfactorBase
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
    fun i =>
      { toRingHom := φRing i
        commutes' := fun s => by
          change φRing i (@algebraMap Q.functionField Γ(D.val.subscheme, ⊤)
            _ _ sourceAlgebra s) = _
          exact (congrArg (fun k : Q.functionField →+* Γ(D.val.subscheme, ⊤) =>
            φRing i (k s)) hmap).trans (hφRing i s) }
  obtain ⟨ell, hell, x, he, hellOne, -, hxC, hpoint⟩ :=
    fixedCurve_factor_normalized_ambient_chart
      (cubic.map a.hom) (hcubic.map a.hom) C hCp
      D.val.subschemeι h hfac
  refine ⟨{
    ell := ell
    hell := hell
    x := x
    he := he
    hellOne := hellOne
    φ := φ
    hzero := ?_
    hambient := ?_ }⟩
  · intro i
    exact eval₂_algHom_eq_zero_of_eval₂_eq_zero q x (φ i) (hxC q hqC)
  · intro i
    let c : Spec (.of Γ(D.val.subscheme, ⊤)) ⟶
        Proj (homogeneousSubmodule (Fin 4) K) :=
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
            (homogeneousSubmodule (Fin 4) Q.functionField)) ≫
        ambientCoefficientMap a.hom
    have hc : c = D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
        hypersurfaceToAmbient (cubic.map a.hom) (hcubic.map a.hom) ≫
          ambientCoefficientMap a.hom := by
      dsimp only [c]
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ ambientCoefficientMap a.hom) hpoint
    have hmarked :=
      quadraticOrderedLiftCoefficientChangedComponentAlgHom_chart_toMarkedPoint
        cubic hcubic a ha z hz i c hc
    simpa only [c, φ, φRing] using hmarked

/-- The fixed-curve factor branch produces a proper relative projective
quadratic family whose universal finite-incidence bad locus contains the
ordered lift of the generic length-eight configuration. -/
theorem exists_fixedCurve_factor_properImageFamily_badLocus
    {K : Type u} [Field K] [CharZero K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    [Infinite (cubicConfigurationBase cubic hcubic 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
      cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 8).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 8 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 8 a ha).val.subschemeι)
    (q : MvPolynomial (Fin 4)
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (hq : q.IsHomogeneous 2) (hqC : q ∈ C.toIdeal) (hq0 : q ≠ 0) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let rC := Module.finrank Q.functionField (homogeneousIdealPiece C 2)
    let hrC : rC ≤ 10 := quadraticSubmodule_finrank_le_ten
      Q.functionField (homogeneousIdealPiece C 2)
    let e := quadraticGrassmannianMonomialEquiv rC hrC
    let marked : Fin 8 →
        (O ⟶ Proj (homogeneousSubmodule (Fin 4) K)) := fun i =>
      @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 8
        (hypersurfaceToAmbient cubic hcubic) i
    letI : Algebra K Q.functionField := a.hom.toAlgebra
    ∃ (U : Q.Opens) (hηU : genericPoint Q ∈ U)
      (f : U.toScheme ⟶ grassmannianScheme K rC (10 - rC)),
      IsProper (grassmannianFrameProjectiveImageFamilyToBase K 2 e f) ∧
      O.fromSpecResidueField z (IsLocalRing.closedPoint (O.residueField z)) ∈
        projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) 2
          (orderedFamilyConfigurationOver
            (hypersurfaceToBase cubic hcubic) 8).hom
          (grassmannianFrameProjectiveImageFamilyToBase K 2 e f)
          marked
          (grassmannianFrameProjectiveImageFamilyToGlobalParameters K 2 e f) ∧
      (projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme)
          (IsLocalRing.closedPoint
            (projectiveConfigurationQuotientOpen
              (grading (equationIdeal cubic hcubic))
              (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField) ∈
        projectiveConfigurationQuotientMap
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8 ''
          projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) 2
            (orderedFamilyConfigurationOver
              (hypersurfaceToBase cubic hcubic) 8).hom
            (grassmannianFrameProjectiveImageFamilyToBase K 2 e f)
            marked
            (grassmannianFrameProjectiveImageFamilyToGlobalParameters K 2 e f) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  let rC := Module.finrank Q.functionField (homogeneousIdealPiece C 2)
  let hrC : rC ≤ 10 := quadraticSubmodule_finrank_le_ten
    Q.functionField (homogeneousIdealPiece C 2)
  let e := quadraticGrassmannianMonomialEquiv rC hrC
  let marked : Fin 8 →
      (O ⟶ Proj (homogeneousSubmodule (Fin 4) K)) := fun i =>
    @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _
      (hypersurfaceToBase cubic hcubic) hsep 8
      (hypersurfaceToAmbient cubic hcubic) i
  letI : Algebra K Q.functionField := a.hom.toAlgebra
  obtain ⟨U, hηU, f, t, q', hq', hq'0, alpha, -, hfbase,
      hproper, -, hqscale, htimage, htparam⟩ :=
    exists_open_fixedCurveQuadraticSystem_properImageFamily_point
      cubic hcubic 8 a ha C q hq hqC hq0
  have hq'C : q' ∈ C.toIdeal := by
    rw [hqscale]
    exact C.toIdeal.mul_mem_left (MvPolynomial.C alpha) hqC
  letI : IsFinite pD := D.property.1
  letI : IsFinite
      (D.val.subschemeι ≫ hypersurfaceToBase
        (cubic.map a.hom) (hcubic.map a.hom)) := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  have hfactorBase : h ≫ toBase C = pD :=
    fixedCurve_factor_toBase (cubic.map a.hom) (hcubic.map a.hom)
      C hCp D.val.subschemeι h hfac
  letI : IsFinite (h ≫ toBase C) := hfactorBase.symm ▸ inferInstance
  letI := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  obtain ⟨incidence⟩ :=
    exists_fixedCurve_factor_ordered_normalized_evaluations
      cubic hcubic a ha z hz C hCp h hfac q' hq' hq'C
  have hrbase : O.fromSpecResidueField z ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).hom =
      Spec.map (CommRingCat.ofHom (b.comp a.hom)) :=
    quadraticOrderedLift_toBase cubic hcubic a ha z hz
  have htbase : t ≫
      grassmannianFrameProjectiveImageFamilyToBase K 2 e f = Spec.map a :=
    fixedCurveQuadraticSystem_properImageFamily_point_toBase
      cubic hcubic a ha hrC e U hηU f t hfbase htimage
  have htframe : t ≫
      grassmannianFrameProjectiveImageFamilyToGlobalParameters K 2 e f =
      projectiveClassifyingMap q' hq' hq'0 a.hom := by
    calc
      _ = projectiveClassifyingMap q' hq' hq'0
          (RingHom.id Q.functionField) ≫
          projectiveParametersCoefficientMap 2
            (algebraMap K Q.functionField) := htparam
      _ = projectiveClassifyingMap q' hq' hq'0 a.hom := by
        exact projectiveClassifyingMap_comp_projectiveParametersCoefficientMap
          2 a.hom q' hq' hq'0
  have hmem := incidence.mem_badLocus_of_familyPoint
    a.hom b rfl q' hq' hq'0
    (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).hom
    (O.fromSpecResidueField z) marked t
    (grassmannianFrameProjectiveImageFamilyToBase K 2 e f)
    (grassmannianFrameProjectiveImageFamilyToGlobalParameters K 2 e f)
    hrbase htbase htframe
  have hmemz : z ∈
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) 2
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase cubic hcubic) 8).hom
        (grassmannianFrameProjectiveImageFamilyToBase K 2 e f)
        marked
        (grassmannianFrameProjectiveImageFamilyToGlobalParameters K 2 e f) := by
    rw [Scheme.fromSpecResidueField_apply z
      (IsLocalRing.closedPoint (O.residueField z))] at hmem
    exact hmem
  refine ⟨U, hηU, f, hproper, hmem, ?_⟩
  exact ⟨z, hmemz, hz⟩

/-- A fixed-curve factor of the original generic configuration cannot have
one of its nonzero quadrics represented by a ground-field frame whose
incidence is excluded at that same generic configuration. This is the exact
assembly endpoint for the divisor-class independence step in Voisin's
argument: once the fixed component is placed in a fixed ground-field linear
system, no second generic configuration is introduced. -/
theorem fixedCurve_factor_groundFrame_member_impossible
    {K : Type u} [Field K] [CharZero K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    [Infinite (cubicConfigurationBase cubic hcubic 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
      cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 8).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 8 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 8 a ha).val.subschemeι)
    (q' : MvPolynomial (Fin 4)
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (hq' : q'.IsHomogeneous 2) (hq'C : q' ∈ C.toIdeal) (hq'0 : q' ≠ 0)
    {m n : ℕ} (e : Fin m ≃ Monomials (Fin 4) 2)
    (q : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (hqli : LinearIndependent K q)
    (t : Spec (.of (cubicConfigurationBase cubic hcubic 8).functionField) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (htbase : t ≫ toBase
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) = Spec.map a)
    (htframe : t ≫ homogeneousFrameToParameters 2 e q hqli =
      projectiveClassifyingMap q' hq' hq'0 a.hom)
    (havoid : ¬ GenericEightConfigurationInHomogeneousFrameIncidence
      cubic hcubic 2 e q hqli) : False := by
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  let marked : Fin 8 →
      (O ⟶ Proj (homogeneousSubmodule (Fin 4) K)) := fun i =>
    @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _
      (hypersurfaceToBase cubic hcubic) hsep 8
      (hypersurfaceToAmbient cubic hcubic) i
  letI : IsFinite pD := D.property.1
  letI : IsFinite
      (D.val.subschemeι ≫ hypersurfaceToBase
        (cubic.map a.hom) (hcubic.map a.hom)) := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  have hfactorBase : h ≫ toBase C = pD :=
    fixedCurve_factor_toBase (cubic.map a.hom) (hcubic.map a.hom)
      C hCp D.val.subschemeι h hfac
  letI : IsFinite (h ≫ toBase C) := hfactorBase.symm ▸ inferInstance
  letI := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  obtain ⟨incidence⟩ :=
    exists_fixedCurve_factor_ordered_normalized_evaluations
      cubic hcubic a ha z hz C hCp h hfac q' hq' hq'C
  have hrbase : O.fromSpecResidueField z ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).hom =
      Spec.map (CommRingCat.ofHom (b.comp a.hom)) :=
    quadraticOrderedLift_toBase cubic hcubic a ha z hz
  have hmem := incidence.mem_badLocus_of_familyPoint
    a.hom b rfl q' hq' hq'0
    (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).hom
    (O.fromSpecResidueField z) marked t
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (homogeneousFrameToParameters 2 e q hqli)
    hrbase htbase htframe
  have hmemz : z ∈
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) 2
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase cubic hcubic) 8).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        marked
        (homogeneousFrameToParameters 2 e q hqli) := by
    rw [Scheme.fromSpecResidueField_apply z
      (IsLocalRing.closedPoint (O.residueField z))] at hmem
    exact hmem
  apply havoid
  exact ⟨z, hmemz, hz⟩

/-- Numerical specialization of
`fixedCurve_factor_groundFrame_member_impossible`. A ground-field polynomial
system of dimension at most eight cannot represent a nonzero member of a
fixed curve containing the original generic length-eight configuration. -/
theorem fixedCurve_factor_groundQuadraticSystem_member_impossible
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic0 : cubic ≠ 0)
    (hcubicPrime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    [Infinite (cubicConfigurationBase cubic hcubic 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
      cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 8).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 8 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 8 a ha).val.subschemeι)
    (q' : MvPolynomial (Fin 4)
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (hq' : q'.IsHomogeneous 2) (hq'C : q' ∈ C.toIdeal) (hq'0 : q' ≠ 0)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ w ∈ W, w.IsHomogeneous 2)
    (hseparate : ∀ w ∈ W,
      w ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → w = 0)
    (hdim : Module.finrank K W ≤ 8)
    {m n : ℕ} (e : Fin m ≃ Monomials (Fin 4) 2)
    (qW : Fin n → W)
    (q : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqliW : LinearIndependent K qW) (hqli : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (t : Spec (.of (cubicConfigurationBase cubic hcubic 8).functionField) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (htbase : t ≫ toBase
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) = Spec.map a)
    (htframe : t ≫ homogeneousFrameToParameters 2 e q hqli =
      projectiveClassifyingMap q' hq' hq'0 a.hom) : False := by
  apply fixedCurve_factor_groundFrame_member_impossible
    cubic hcubic a ha z hz C hCp h hfac q' hq' hq'C hq'0 e q hqli
      t htbase htframe
  exact not_genericEightConfigurationInHomogeneousFrameIncidence_of_finrank_le_eight
    cubic hcubic hcubic0 hcubicPrime (by decide) W hhom hseparate hdim
      qW q hq hqliW hqli hn e

end PfaffianDescent

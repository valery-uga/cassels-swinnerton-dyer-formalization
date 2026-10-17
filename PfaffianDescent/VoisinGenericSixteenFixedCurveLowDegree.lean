import PfaffianDescent.VoisinGenericSixteenLowDegreeDetection
import PfaffianDescent.VoisinGenericDegreeEightFixedCurveDichotomy

/-!
# Low-degree equations of a fixed curve through the generic sixteen points

The ordered-lift detector works on the normalized chart supplied by a
fixed-curve factorization. Consequently, if the transported frame spans,
that curve has no nonzero equation of the detected degree.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The normalized projective map depends on an algebra structure only
through that structure; proof fields of its chart certificate are irrelevant. -/
theorem linearNormalizedPointAt_eq_of_algebra_eq
    {F A : Type u} [Field F] [CommRing A]
    {σ : Type}
    (B₁ B₂ : Algebra F A) (hB : B₁ = B₂)
    (I : HomogeneousIdeal (homogeneousSubmodule σ F))
    (x : σ → A)
    (he₁ : ∀ q ∈ I.toIdeal, q.eval₂ (@algebraMap F A _ _ B₁) x = 0)
    (he₂ : ∀ q ∈ I.toIdeal, q.eval₂ (@algebraMap F A _ _ B₂) x = 0)
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hOne₁ : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (@algebraMap F A _ _ B₁) x) he₁) z = 1)
    (hOne₂ : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (@algebraMap F A _ _ B₂) x) he₂) z = 1) :
    @linearNormalizedPointAt F A _ _ B₁ σ I x he₁ z hz hOne₁ =
      @linearNormalizedPointAt F A _ _ B₂ σ I x he₂ z hz hOne₂ := by
  subst B₂
  rfl

/-- A fixed curve containing the actual generic sixteen-point scheme cannot
have a nonzero equation in any degree detected by a spanning ordered-lift
frame. -/
theorem cubicSixteenFixedCurve_no_nonzero_homogeneous_equation_of_detectedFrame
    {K : Type u} [Field K]
    {d n m : ℕ}
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
    (e : Fin m ≃ Monomials (Fin 4) d)
    (frame : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hframe : LinearIndependent K frame)
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt cubic hcubic e frame hframe z)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 16 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι)
    (r : MvPolynomial (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (hr : r.IsHomogeneous d) (hrC : r ∈ C.toIdeal) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    (hspan : Submodule.span Q.functionField
      (Set.range (fun i => homogeneousSubmoduleBaseChange (σ := Fin 4) d a.hom
        (frame i))) = ⊤) → r = 0 := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsFinite
      (D.val.subschemeι ≫ hypersurfaceToBase
        (cubic.map a.hom) (hcubic.map a.hom)) := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  let canonicalAlgebra := finiteSchemeCoefficientAlgebra pD
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
  have hAlg : sourceAlgebra = canonicalAlgebra := by
    dsimp only [sourceAlgebra, canonicalAlgebra]
    simpa only [hfactorBase]
  obtain ⟨ell, hell, x, he, hellOne, -, hxC, hpoint⟩ :=
    fixedCurve_factor_normalized_ambient_chart
      (cubic.map a.hom) (hcubic.map a.hom) C hCp
      D.val.subschemeι h hfac
  intro hspan
  letI := canonicalAlgebra
  have he' : ∀ q ∈ (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal,
      (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) q = 0 := by
    simpa only [← hmap] using he
  have hellOne' : (Ideal.Quotient.lift
      (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal
      (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) he')
        (Ideal.Quotient.mk
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell) = 1 := by
    simpa only [← hmap] using hellOne
  have hpoint' :
      linearNormalizedPointAt
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField))
          x he'
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell)
          (polynomial_class_mem_grading
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)) ell hell)
          hellOne' ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField)) =
        D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient (cubic.map a.hom) (hcubic.map a.hom) := by
    have hchart := linearNormalizedPointAt_eq_of_algebra_eq
      sourceAlgebra canonicalAlgebra hAlg
      (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) Q.functionField))
      x he he'
      (Ideal.Quotient.mk
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell)
      (polynomial_class_mem_grading
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField)) ell hell)
      hellOne hellOne'
    rw [hchart] at hpoint
    exact hpoint
  have hinj := cubicSixteenOrderedLift_normalizedAmbientChart_restriction_injective
    cubic hcubic a ha z hz e frame hframe hno hspan
      ell hell x he' hellOne' hpoint'
  have hzero : homogeneousSectionRestriction (K := Q.functionField) x d
      (⟨r, hr⟩ : homogeneousSubmodule (Fin 4) Q.functionField d) = 0 := by
    change r.eval₂ (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 0
    simpa only [← hmap] using hxC r hrC
  have heq : (⟨r, hr⟩ : homogeneousSubmodule (Fin 4) Q.functionField d) = 0 :=
    hinj (by simpa only [map_zero] using hzero)
  exact congrArg Subtype.val heq


/-- A fixed curve through the actual generic sixteen-point scheme has no
nonzero linear or quadratic homogeneous equation. The ordered lift and its
full frame are selected internally. -/
theorem cubicConfigurationGenericSixteen_fixedCurve_no_lowDegree_equation
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
    (e : Fin m ≃ Monomials (Fin 4) d)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 16 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι)
    (r : MvPolynomial (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (hr : r.IsHomogeneous d) (hrC : r ∈ C.toIdeal) : r = 0 := by
  let Q := cubicConfigurationBase cubic hcubic 16
  letI : Algebra K Q.functionField := a.hom.toAlgebra
  let frame := Module.finBasis K (homogeneousSubmodule (Fin 4) K d)
  obtain ⟨z, hz, hno⟩ :=
    exists_orderedPointOver_genericSixteen_with_noCommonLowDegreeEquation
      cubic hcubic hcubic_ne hcubic_prime hd hd3 e
  have hspan : Submodule.span Q.functionField
      (Set.range (fun i => homogeneousSubmoduleBaseChange (σ := Fin 4) d a.hom
        (frame i))) = ⊤ := by
    have hbase := homogeneousFrame_baseChange_span_top
      (K := K) (L := Q.functionField) e frame
    rw [show algebraMap K Q.functionField = a.hom by rfl] at hbase
    exact hbase
  exact cubicSixteenFixedCurve_no_nonzero_homogeneous_equation_of_detectedFrame
    cubic hcubic a ha z hz e frame frame.linearIndependent hno
      C hCp h hfac r hr hrC hspan


/-- The low-degree homogeneous pieces of the ideal of any fixed curve
containing the generic sixteen-point scheme are zero. This is the Hilbert
function form of the equation-level exclusion. -/
theorem cubicConfigurationGenericSixteen_fixedCurve_lowDegreePiece_eq_bot
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
    (e : Fin m ≃ Monomials (Fin 4) d)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 16 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι)
    : homogeneousIdealPiece C d = ⊥ := by
  apply le_antisymm
  · intro q hq
    change q = 0
    apply Subtype.ext
    exact cubicConfigurationGenericSixteen_fixedCurve_no_lowDegree_equation
      cubic hcubic hcubic_ne hcubic_prime a ha hd hd3 e
        C hCp h hfac q.val q.property
        ((mem_homogeneousIdealPiece_iff C d q).mp hq)
  · exact bot_le


/-- The coordinate ring of such a fixed curve has the full ambient Hilbert
function in degrees one and two; no low-degree equation is lost. -/
theorem cubicConfigurationGenericSixteen_fixedCurve_lowDegreeHilbertFunction
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
    (e : Fin m ≃ Monomials (Fin 4) d)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 16 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι)
    : Module.finrank (cubicConfigurationBase cubic hcubic 16).functionField
        (homogeneousSubmodule (Fin 4)
          (cubicConfigurationBase cubic hcubic 16).functionField d ⧸
          homogeneousIdealPiece C d) = (d + 3).choose 3 := by
  let F := (cubicConfigurationBase cubic hcubic 16).functionField
  letI : FiniteDimensional F (homogeneousSubmodule (Fin 4) F d) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) F d)
  have hpiece : homogeneousIdealPiece C d = ⊥ :=
    cubicConfigurationGenericSixteen_fixedCurve_lowDegreePiece_eq_bot
      cubic hcubic hcubic_ne hcubic_prime a ha hd hd3 e C hCp h hfac
  rw [Submodule.finrank_quotient, hpiece]
  simpa using
    four_variable_homogeneous_finrank (K := F) d


/-- The generic sixteen-point subscheme is disjoint from any homogeneous
closed subscheme of its cubic surface carrying a nonzero linear or quadratic
equation. The single-closed-point dichotomy rules out the factor branch. -/
theorem cubicConfigurationGenericSixteen_misses_fixedCurve_with_lowDegree_equation
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
    [hordered : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {d m : ℕ} (hd : 0 < d) (hd3 : d < 3)
    (e : Fin m ≃ Monomials (Fin 4) d)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (r : MvPolynomial (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (hr : r.IsHomogeneous d) (hrC : r ∈ C.toIdeal) (hrne : r ≠ 0) :
    IsEmpty (pullback
      (homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp)
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι : Scheme.{u}) := by
  letI : IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal cubic hcubic)) 16).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left
    exact hordered
  let j := homogeneousFixedCurveToCubic
    (cubic.map a.hom) (hcubic.map a.hom) C hCp
  letI : IsClosedImmersion j :=
    homogeneousFixedCurveToCubic_closedImmersion
      (cubic.map a.hom) (hcubic.map a.hom) C hCp
  rcases cubicConfigurationGenericFiniteSubscheme_isEmpty_pullback_or_factors
      cubic hcubic 16 a ha (0 : Fin 16) j with hmiss | ⟨h, hfac⟩
  · exact hmiss
  · exfalso
    exact hrne (cubicConfigurationGenericSixteen_fixedCurve_no_lowDegree_equation
      cubic hcubic hcubic_ne hcubic_prime a ha hd hd3 e
        C hCp h hfac r hr hrC)

/-- An ideal generated by its quadratic piece is zero when that piece is
zero. This packages the ideal-theoretic step needed for quadratic curve
presentations. -/
theorem homogeneousIdeal_toIdeal_eq_bot_of_quadraticPiece_eq_bot
    {F : Type u} [Field F]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hgen : quadraticPieceGenerates C)
    (hpiece : homogeneousIdealPiece C 2 = ⊥) : C.toIdeal = ⊥ := by
  change C.toIdeal = Ideal.span
    (Set.range fun q : homogeneousIdealPiece C 2 => q.val.val) at hgen
  rw [hgen]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro r ⟨q, rfl⟩
    have hq : (q.val : homogeneousSubmodule (Fin 4) F 2) = 0 := by
      have hmem : q.val ∈ (⊥ : Submodule F
          (homogeneousSubmodule (Fin 4) F 2)) := by
        rw [← hpiece]
        exact q.property
      exact (Submodule.mem_bot F).mp hmem
    exact (Ideal.mem_bot).mpr (congrArg Subtype.val hq)
  · exact bot_le


/-- A fixed curve whose ideal is generated by quadrics cannot meet the
generic sixteen-point configuration. In particular, this applies once an
intrinsic curve presentation proves quadratic generation. -/
theorem cubicConfigurationGenericSixteen_misses_quadraticallyGeneratedCurve
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
    [hordered : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 2)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (hgen : quadraticPieceGenerates C) :
    IsEmpty (pullback
      (homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp)
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι : Scheme.{u}) := by
  letI : IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal cubic hcubic)) 16).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 16).left
    exact hordered
  let j := homogeneousFixedCurveToCubic
    (cubic.map a.hom) (hcubic.map a.hom) C hCp
  letI : IsClosedImmersion j :=
    homogeneousFixedCurveToCubic_closedImmersion
      (cubic.map a.hom) (hcubic.map a.hom) C hCp
  rcases cubicConfigurationGenericFiniteSubscheme_isEmpty_pullback_or_factors
      cubic hcubic 16 a ha (0 : Fin 16) j with hmiss | ⟨h, hfac⟩
  · exact hmiss
  · exfalso
    have hpiece : homogeneousIdealPiece C 2 = ⊥ :=
      cubicConfigurationGenericSixteen_fixedCurve_lowDegreePiece_eq_bot
        cubic hcubic hcubic_ne hcubic_prime a ha
          (by decide) (by decide) e C hCp h hfac
    have hbot := homogeneousIdeal_toIdeal_eq_bot_of_quadraticPiece_eq_bot
      C hgen hpiece
    have hp0 : cubic.map a.hom ≠ 0 :=
      cubicConfigurationCoefficientChange_ne_zero cubic hcubic 16 a hcubic_ne
    exact hp0 ((Ideal.mem_bot).mp (hbot ▸ hCp))

end PfaffianDescent

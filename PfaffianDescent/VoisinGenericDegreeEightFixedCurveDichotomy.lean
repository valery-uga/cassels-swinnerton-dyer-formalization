import PfaffianDescent.VoisinGenericCubicPoint
import PfaffianDescent.VoisinDegreeEightFixedCurveScheme
import PfaffianDescent.VoisinDegreeEightFixedCurveSections
import PfaffianDescent.VoisinDegreeEightFixedComponentGenericity
import PfaffianDescent.FiniteProjectiveCoordinates
import PfaffianDescent.FiniteProjectiveNormalizedCoordinates
import PfaffianDescent.VoisinGenericGrassmannianSpread

/-!
# The generic fixed curve meets all eight points or none

The prime divisor extracted from a failed quadratic system is a closed
subscheme of the coefficient-changed cubic. The generic configuration is one
closed point, so this divisor either misses that configuration or contains
the entire finite scheme. This is Voisin's scheme-theoretic fixed-component
dichotomy.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The common prime divisor extracted from a failed generic quadratic
system, together with the all-or-none alternative for the rank-eight datum. -/
structure DegreeEightFixedCurveDichotomyData
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)] where
  x : Fin 4 → Γ(D₈.val.subscheme, ⊤)
  q : MvPolynomial (Fin 4) F
  C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) F)
  hCp : p ∈ C.toIdeal
  evaluationSurjective :
    Function.Surjective (eval₂Hom (algebraMap F Γ(D₈.val.subscheme, ⊤)) x)
  fixedSubscheme : DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp
  allOrNone :
    IsEmpty (pullback (homogeneousFixedCurveToCubic p hp C hCp)
        D₈.val.subschemeι : Scheme.{u}) ∨
      ∃ h : D₈.val.subscheme ⟶ scheme C,
        h ≫ homogeneousFixedCurveToCubic p hp C hCp = D₈.val.subschemeι

/-- The distinguished nonzero quadric in a fixed-curve dichotomy is an
actual point of the projective family over the associated Grassmannian
point, with its ambient equation tracked exactly up to a nonzero scalar. -/
theorem DegreeEightFixedCurveDichotomyData.exists_distinguished_projective_point
    {F : Type u} [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)]
    (D : DegreeEightFixedCurveDichotomyData p hp D₈) :
    let r := Module.finrank F (homogeneousIdealPiece D.C 2)
    let hr : r ≤ 10 := quadraticSubmodule_finrank_le_ten F
      (homogeneousIdealPiece D.C 2)
    let e := quadraticGrassmannianMonomialEquiv r hr
    ∃ (t : Spec (.of F) ⟶
        grassmannianFrameProjectiveFamilyPullback K 2 e
          (grassmannianQuotientMorphism (A := F) K
            (fixedCurveQuadraticGrassmannian F D.C)))
      (q' : MvPolynomial (Fin 4) F) (hq' : q'.IsHomogeneous 2)
      (hq'0 : q' ≠ 0) (alpha : F),
      alpha ≠ 0 ∧ q' = MvPolynomial.C alpha * D.q ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToBase K 2 e
          (grassmannianQuotientMorphism (A := F) K
            (fixedCurveQuadraticGrassmannian F D.C)) = 𝟙 _ ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K 2 e
          (grassmannianQuotientMorphism (A := F) K
            (fixedCurveQuadraticGrassmannian F D.C)) =
        projectiveClassifyingMap q' hq' hq'0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap 2 (algebraMap K F) := by
  obtain ⟨hq, _, hq0, _, _, _, _, _, _, hspan, _, _, _⟩ := D.fixedSubscheme
  have hqC : D.q ∈ D.C.toIdeal := hspan (Ideal.subset_span (by simp))
  exact exists_fixedCurveQuadraticGrassmannian_projective_point
    (K := K) D.C D.q hq hqC hq0

/-- The quadratic system of the fixed curve in a degree-eight dichotomy has
at most eight independent sections.  This makes the numerical input from the
fixed-curve construction available directly from the all-or-none package. -/
theorem DegreeEightFixedCurveDichotomyData.not_nine_le_finrank_fixedCurveQuadraticPolynomialSystem
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)]
    (D : DegreeEightFixedCurveDichotomyData p hp D₈) :
    ¬ 9 ≤ Module.finrank F (fixedCurveQuadraticPolynomialSystem D.C) := by
  exact D.fixedSubscheme.not_nine_le_finrank_fixedCurveQuadraticPolynomialSystem
    p hp D₈ D.x D.q D.C D.hCp

/-- Equivalently, the fixed-curve quadratic system in the dichotomy has
dimension at most eight.  This is the numerical form required when applying
the bounded-family generic-incidence API. -/
theorem DegreeEightFixedCurveDichotomyData.finrank_fixedCurveQuadraticPolynomialSystem_le_eight
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)]
    (D : DegreeEightFixedCurveDichotomyData p hp D₈) :
    Module.finrank F (fixedCurveQuadraticPolynomialSystem D.C) ≤ 8 := by
  exact D.fixedSubscheme.finrank_fixedCurveQuadraticPolynomialSystem_le_eight
    p hp D₈ D.x D.q D.C D.hCp

/-- Every quadratic vanishing on the rank-eight datum belongs to the
quadratic system of its fixed curve.  This is the algebraic containment that
the all-or-none alternative must transport to the generic incidence family. -/
theorem DegreeEightFixedCurveDichotomyData.vanishingQuadrics_mem_fixedCurveQuadraticPolynomialSystem
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)]
    (D : DegreeEightFixedCurveDichotomyData p hp D₈)
    (r : MvPolynomial (Fin 4) F)
    (hr : r ∈ homogeneousVanishingPolynomialSubmodule
      (K := F) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) D.x 2) :
    r ∈ fixedCurveQuadraticPolynomialSystem D.C := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcontains⟩ := D.fixedSubscheme
  obtain ⟨hrhom, hrC, _⟩ := hcontains r hr
  exact (mem_fixedCurveQuadraticPolynomialSystem_iff D.C r).mpr ⟨hrhom, hrC⟩

/-- A factorization of a finite subscheme through a homogeneous fixed curve
is compatible with the structural maps to the ground field. -/
theorem fixedCurve_factor_toBase
    {F : Type u} [Field F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) F))
    (hCp : p ∈ C.toIdeal) {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface p hp)
    (h : Z ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic p hp C hCp = i) :
    h ≫ toBase C = i ≫ hypersurfaceToBase p hp := by
  let j := homogeneousFixedCurveToCubic p hp C hCp
  have hj : j ≫ hypersurfaceToBase p hp = toBase C := by
    rw [show j = homogeneousFixedCurveToCubic p hp C hCp from rfl]
    exact schemeQuotientMap_toBase (equationIdeal p hp) C
      (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)
  calc
    h ≫ toBase C = h ≫ (j ≫ hypersurfaceToBase p hp) := by rw [hj]
    _ = (h ≫ j) ≫ hypersurfaceToBase p hp := (Category.assoc _ _ _).symm
    _ = i ≫ hypersurfaceToBase p hp := by rw [hfac]

/-- If a finite closed subscheme of a cubic factors through a homogeneous
fixed curve, it has canonical projective coordinates in which every
homogeneous equation of that curve vanishes. -/
theorem fixedCurve_factor_coordinates
    {F : Type u} [Field F] [Infinite F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) F))
    (hCp : p ∈ C.toIdeal) {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface p hp)
    [IsClosedImmersion i] [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (h : Z ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic p hp C hCp = i) :
    letI : IsFinite (h ≫ toBase C) :=
      (fixedCurve_factor_toBase p hp C hCp i h hfac).symm ▸ inferInstance
    letI := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
    ∃ x : Fin 4 → Γ(Z, ⊤),
      Function.Surjective (eval₂Hom (algebraMap F Γ(Z, ⊤)) x) ∧
        ∀ (r : MvPolynomial (Fin 4) F) (d : ℕ), r.IsHomogeneous d → r ∈ C.toIdeal →
          r.eval₂ (algebraMap F Γ(Z, ⊤)) x = 0 := by
  let j := homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion j :=
    homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  haveI : IsClosedImmersion (h ≫ j) := by
    rw [show j = homogeneousFixedCurveToCubic p hp C hCp from rfl, hfac]
    infer_instance
  letI : IsClosedImmersion h := IsClosedImmersion.of_comp h j
  letI : IsFinite (h ≫ toBase C) :=
    (fixedCurve_factor_toBase p hp C hCp i h hfac).symm ▸ inferInstance
  exact finite_projective_closed_subscheme_coordinates C h

/-- The coordinates supplied by a factorization through a fixed curve can
also be read in the canonical coefficient algebra induced by the original
finite subscheme in the cubic. -/
theorem fixedCurve_factor_coordinates_ambient
    {F : Type u} [Field F] [Infinite F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) F))
    (hCp : p ∈ C.toIdeal) {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface p hp)
    [IsClosedImmersion i] [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (h : Z ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic p hp C hCp = i) :
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ x : Fin 4 → Γ(Z, ⊤),
      Function.Surjective (eval₂Hom (algebraMap F Γ(Z, ⊤)) x) ∧
        ∀ (r : MvPolynomial (Fin 4) F) (d : ℕ), r.IsHomogeneous d → r ∈ C.toIdeal →
          r.eval₂ (algebraMap F Γ(Z, ⊤)) x = 0 := by
  have hbase := fixedCurve_factor_toBase p hp C hCp i h hfac
  letI : IsFinite (h ≫ toBase C) := hbase.symm ▸ inferInstance
  letI := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
  obtain ⟨x, hx, hxC⟩ := fixedCurve_factor_coordinates p hp C hCp i h hfac
  have hmap := finiteSchemeCoefficient_algebraMap_eq_of_eq
    (h ≫ toBase C) (i ≫ hypersurfaceToBase p hp) hbase
  refine ⟨x, ?_, ?_⟩
  · rw [← hmap]
    exact hx
  · intro r d hr hC
    rw [← hmap]
    exact hxC r d hr hC

/-- A factorization through a homogeneous fixed curve supplies one normalized
ambient projective chart which recovers the original finite-scheme immersion
and on which every equation of the fixed curve vanishes. -/
theorem fixedCurve_factor_normalized_ambient_chart
    {F : Type u} [Field F] [Infinite F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) F))
    (hCp : p ∈ C.toIdeal) {Z : Scheme.{u}}
    (i : Z ⟶ hypersurface p hp)
    [IsClosedImmersion i] [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (h : Z ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic p hp C hCp = i) :
    letI : IsAffine Z :=
      isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
    letI : IsFinite (h ≫ toBase C) :=
      (fixedCurve_factor_toBase p hp C hCp i h hfac).symm ▸ inferInstance
    letI := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
    ∃ (ell : MvPolynomial (Fin 4) F) (hell : ell.IsHomogeneous 1)
      (x : Fin 4 → Γ(Z, ⊤))
      (he₀ : ∀ q ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) F)).toIdeal,
        (eval₂Hom (algebraMap F Γ(Z, ⊤)) x) q = 0)
      (hellOne : (Ideal.Quotient.lift
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)).toIdeal
        (eval₂Hom (algebraMap F Γ(Z, ⊤)) x) he₀)
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) F)).toIdeal ell) = 1),
      Function.Surjective (eval₂Hom (algebraMap F Γ(Z, ⊤)) x) ∧
      (∀ q ∈ C.toIdeal,
        q.eval₂ (algebraMap F Γ(Z, ⊤)) x = 0) ∧
      linearNormalizedPointAt
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
          x he₀
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) F)).toIdeal ell)
          (polynomial_class_mem_grading
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
            ell hell) hellOne ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) =
        Z.isoSpec.inv ≫ i ≫ hypersurfaceToAmbient p hp := by
  letI : IsAffine Z :=
    isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  have hbase := fixedCurve_factor_toBase p hp C hCp i h hfac
  let j := homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion j :=
    homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  haveI : IsClosedImmersion (h ≫ j) := by
    rw [show j = homogeneousFixedCurveToCubic p hp C hCp from rfl, hfac]
    infer_instance
  letI : IsClosedImmersion h := IsClosedImmersion.of_comp h j
  letI : IsFinite (h ≫ toBase C) := hbase.symm ▸ inferInstance
  letI := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
  obtain ⟨ell, hell, x, he₀, hellOne, hx, hxC, hpoint⟩ :=
    finite_projective_closed_subscheme_normalized_ambient_chart C h
  refine ⟨ell, hell, x, he₀, hellOne, hx, hxC, ?_⟩
  calc
      _ = Z.isoSpec.inv ≫ h ≫ quotientProjMap C := hpoint
      _ = Z.isoSpec.inv ≫ h ≫
          (homogeneousFixedCurveToCubic p hp C hCp ≫
            hypersurfaceToAmbient p hp) := by
        rw [homogeneousFixedCurveToCubic_comp_hypersurfaceToAmbient]
      _ = Z.isoSpec.inv ≫
          (h ≫ homogeneousFixedCurveToCubic p hp C hCp) ≫
            hypersurfaceToAmbient p hp := by simp only [Category.assoc]
      _ = Z.isoSpec.inv ≫ i ≫ hypersurfaceToAmbient p hp := by rw [hfac]

/-- The factor branch of a degree-eight fixed-curve dichotomy supplies
ambient canonical coordinates on which the whole fixed-curve ideal vanishes. -/
theorem DegreeEightFixedCurveDichotomyData.factor_coordinates_ambient
    {F : Type u} [Field F] [Infinite F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)]
    (D : DegreeEightFixedCurveDichotomyData p hp D₈)
    (h : D₈.val.subscheme ⟶ scheme D.C)
    (hfac : h ≫ homogeneousFixedCurveToCubic p hp D.C D.hCp = D₈.val.subschemeι) :
    let C := D.C
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
      Function.Surjective (eval₂Hom (algebraMap F Γ(D₈.val.subscheme, ⊤)) x) ∧
        ∀ (r : MvPolynomial (Fin 4) F) (d : ℕ), r.IsHomogeneous d → r ∈ C.toIdeal →
          r.eval₂ (algebraMap F Γ(D₈.val.subscheme, ⊤)) x = 0 := by
  exact fixedCurve_factor_coordinates_ambient p hp D.C D.hCp
    D₈.val.subschemeι h hfac

/-- A scalar multiple of the distinguished fixed quadric still vanishes on
any normalized coordinates on which that quadric vanishes.  This is the
evaluation statement used after transporting the distinguished member into
the proper projective family. -/
theorem DegreeEightFixedCurveDichotomyData.scaled_distinguished_evaluation_eq_zero
    {F : Type u} [Field F] [Infinite F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)]
    (D : DegreeEightFixedCurveDichotomyData p hp D₈)
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (q' : MvPolynomial (Fin 4) F) (alpha : F)
    (hq' : q' = MvPolynomial.C alpha * D.q)
    (hqzero : D.q.eval₂ (algebraMap F Γ(D₈.val.subscheme, ⊤)) x = 0) :
    q'.eval₂ (algebraMap F Γ(D₈.val.subscheme, ⊤)) x = 0 := by
  rw [hq', MvPolynomial.eval₂_mul]
  rw [hqzero, mul_zero]

/-- In the factor branch, the normalized coordinates can be chosen so that
the member transported into the proper projective family vanishes on the
whole rank-eight datum. -/
theorem DegreeEightFixedCurveDichotomyData.exists_factor_coordinates_scaled_distinguished_vanishes
    {F : Type u} [Field F] [Infinite F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)]
    (D : DegreeEightFixedCurveDichotomyData p hp D₈)
    (h : D₈.val.subscheme ⟶ scheme D.C)
    (hfac : h ≫ homogeneousFixedCurveToCubic p hp D.C D.hCp =
      D₈.val.subschemeι)
    (q' : MvPolynomial (Fin 4) F) (alpha : F)
    (hq' : q' = MvPolynomial.C alpha * D.q) :
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
      Function.Surjective (eval₂Hom (algebraMap F Γ(D₈.val.subscheme, ⊤)) x) ∧
        q'.eval₂ (algebraMap F Γ(D₈.val.subscheme, ⊤)) x = 0 := by
  let C := D.C
  let hCp := D.hCp
  let q := D.q
  obtain ⟨hqhom, _, _, _, _, _, _, _, _, hspan, _, _, _⟩ := D.fixedSubscheme
  have hqC0 : D.q ∈ D.C.toIdeal :=
    hspan (Ideal.subset_span (Or.inr rfl))
  have hqC : q ∈ C.toIdeal := hqC0
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hxsurj, hxC⟩ := fixedCurve_factor_coordinates_ambient
    p hp C hCp D₈.val.subschemeι h hfac
  refine ⟨x, hxsurj, ?_⟩
  rw [hq', MvPolynomial.eval₂_mul]
  rw [hxC q 2 hqhom hqC, mul_zero]

/-- In the factor branch, every quadratic equation of the fixed curve lies
in the degree-two vanishing system of canonical coordinates on the finite
datum. -/
theorem DegreeEightFixedCurveDichotomyData.factor_fixedCurveQuadraticPolynomialSystem_le_vanishing
    {F : Type u} [Field F] [Infinite F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)]
    (D : DegreeEightFixedCurveDichotomyData p hp D₈)
    (h : D₈.val.subscheme ⟶ scheme D.C)
    (hfac : h ≫ homogeneousFixedCurveToCubic p hp D.C D.hCp = D₈.val.subschemeι) :
    let C := D.C
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
      Function.Surjective (eval₂Hom (algebraMap F Γ(D₈.val.subscheme, ⊤)) x) ∧
        fixedCurveQuadraticPolynomialSystem C ≤
          homogeneousVanishingPolynomialSubmodule
            (K := F) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 := by
  let C := D.C
  let hCp := D.hCp
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI : Module.Finite F Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hx, hxC⟩ := fixedCurve_factor_coordinates_ambient
    p hp C hCp D₈.val.subschemeι h hfac
  refine ⟨x, hx, ?_⟩
  intro r hr
  obtain ⟨hrhom, hrC⟩ := (mem_fixedCurveQuadraticPolynomialSystem_iff C r).mp hr
  exact (mem_homogeneousVanishingPolynomialSubmodule_iff
    (K := F) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 r).mpr
      ⟨hrhom, hxC r 2 hrhom hrC⟩

/-- The all-or-none alternative for the fixed curve is usable directly in
the ambient canonical coefficient algebra: either the curve misses the
finite datum, or all of its homogeneous equations vanish on suitable
projective coordinates of that datum. -/
theorem DegreeEightFixedCurveDichotomyData.allOrNone_coordinates_ambient
    {F : Type u} [Field F] [Infinite F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)]
    (D : DegreeEightFixedCurveDichotomyData p hp D₈) :
    let C := D.C
    let hCp := D.hCp
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    IsEmpty (pullback (homogeneousFixedCurveToCubic p hp C hCp)
        D₈.val.subschemeι : Scheme.{u}) ∨
      ∃ x : Fin 4 → Γ(D₈.val.subscheme, ⊤),
        Function.Surjective (eval₂Hom (algebraMap F Γ(D₈.val.subscheme, ⊤)) x) ∧
          ∀ (r : MvPolynomial (Fin 4) F) (d : ℕ), r.IsHomogeneous d → r ∈ C.toIdeal →
            r.eval₂ (algebraMap F Γ(D₈.val.subscheme, ⊤)) x = 0 := by
  rcases D.allOrNone with hmiss | ⟨h, hfac⟩
  · exact Or.inl hmiss
  · exact Or.inr (D.factor_coordinates_ambient p hp D₈ h hfac)

/-- A framed quadratic system containing the fixed curve of a degree-eight
fixed-component datum cannot contain the generic length-eight configuration.
This is the numerical half of Voisin's fixed-component contradiction: the
remaining geometric step is to construct the frame and its incidence from
the moving divisor family. -/
theorem DegreeEightFixedCurveDichotomyData.not_genericEightConfigurationInHomogeneousFrameIncidence
    {F : Type u} [Field F] [IsAlgClosed F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) F))).IsPrime)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra F Γ(D₈.val.subscheme, ⊤)]
    (D : DegreeEightFixedCurveDichotomyData p hp D₈)
    {m n : ℕ} (e : Fin m ≃ Monomials (Fin 4) 2)
    (qW : Fin n → fixedCurveQuadraticPolynomialSystem D.C)
    (q : Fin n → homogeneousSubmodule (Fin 4) F 2)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) F) = (q j).1)
    (hqli : LinearIndependent F qW) (hqliq : LinearIndependent F q)
    (hn : Module.finrank F (fixedCurveQuadraticPolynomialSystem D.C) = n)
    [IsSeparated (hypersurfaceToBase p hp)]
    [LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme] :
    ¬ GenericEightConfigurationInHomogeneousFrameIncidence p hp 2 e q hqliq := by
  exact not_genericEightConfigurationInHomogeneousFrameIncidence_of_finrank_le_eight
    p hp hp0 hprime (by decide) (fixedCurveQuadraticPolynomialSystem D.C)
      (fixedCurveQuadraticPolynomialSystem_isHomogeneous D.C)
      (fixedCurveQuadraticPolynomialSystem_separates_cubic p hp D.C)
      (D.finrank_fixedCurveQuadraticPolynomialSystem_le_eight p hp D₈)
      qW q hq hqli hqliq hn e

/-- Every homogeneous fixed curve on the generic coefficient-changed cubic
satisfies Voisin's all-or-none alternative. The second branch is an actual
factorization of the whole rank-eight finite scheme through the curve. -/
theorem genericDegreeEightFixedCurve_all_or_none_of_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫ cubicConfigurationToBase p hp 8)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule
        (Fin 4) (cubicConfigurationBase p hp 8).functionField))
      (hCp : p.map a.hom ∈ C.toIdeal),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      IsEmpty
          (pullback
            (homogeneousFixedCurveToCubic (p.map a.hom) (hp.map a.hom) C hCp)
            Dη.val.subschemeι : Scheme.{u}) ∨
        ∃ h : Dη.val.subscheme ⟶ scheme C,
          h ≫ homogeneousFixedCurveToCubic
              (p.map a.hom) (hp.map a.hom) C hCp = Dη.val.subschemeι := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 8 D₈
  intro a ha C hCp
  dsimp only
  letI : IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 8).left :=
    isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
      p hp hp0 8 D₈
  let j := homogeneousFixedCurveToCubic (p.map a.hom) (hp.map a.hom) C hCp
  letI : IsClosedImmersion j :=
    homogeneousFixedCurveToCubic_closedImmersion (p.map a.hom) (hp.map a.hom) C hCp
  exact cubicConfigurationGenericFiniteSubscheme_isEmpty_pullback_or_factors
    p hp 8 a ha (0 : Fin 8) j

/-- Failure of the no-common-curve condition on the generic degree-eight
configuration produces the complete fixed-divisor profile and Voisin's
all-or-none alternative in one checked object. -/
theorem nonempty_genericDegreeEightFixedCurveDichotomyData_of_not_noCommonCurve
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫ cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : IsFinite
          (Dη.val.subschemeι ≫ hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
        Dη.property.1
      letI := finiteSchemeCoefficientAlgebra
        (Dη.val.subschemeι ≫ hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      ¬ DegreeEightQuadraticSystemHasNoCommonCurveComponent
          (p.map a.hom) (hp.map a.hom) Dη →
        Nonempty (DegreeEightFixedCurveDichotomyData
          (p.map a.hom) (hp.map a.hom) Dη) := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 8 D₈
  intro a ha
  dsimp only
  intro hcommon
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 8 a
  have hpη0 : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hp0
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  letI : IsFinite
      (Dη.val.subschemeι ≫ hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    Dη.property.1
  letI := finiteSchemeCoefficientAlgebra
    (Dη.val.subschemeι ≫ hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  obtain ⟨x, q, C, hCp, hx, hfixed⟩ :=
    exists_degreeEightDivisorFixedSubschemeData_of_not_noCommonCurveComponent_on_smoothCubic
      (p.map a.hom) (hp.map a.hom) hpη0 Dη hcommon
  have hall := genericDegreeEightFixedCurve_all_or_none_of_smooth
    p hp hp0 D₈ a ha C hCp
  exact ⟨⟨x, q, C, hCp, hx, hfixed, hall⟩⟩

end PfaffianDescent

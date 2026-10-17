import PfaffianDescent.VoisinGenericQuadraticEvaluation
import PfaffianDescent.VoisinSectionChoice

/-!
# Detection of the quadratic frame on the ordered generic eight points

This file assembles the normalized-chart and projective-parameter bridges into
the injectivity statement used in Voisin's degree-eight argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An ordered lift of the generic point of a configuration quotient remains
over the original affine base after composing the two induced ring maps. -/
lemma projectiveConfigurationOrderedLift_toBase
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A)
    [GradedRing 𝒜]
    (f : Proj 𝒜 ⟶ Spec (.of K)) (n : ℕ) [IsSeparated f]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField)
    (ha : Spec.map a =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) ≫
        projectiveConfigurationQuotientToBase 𝒜 f n)
    (z : (orderedFamilyConfigurationOver f n).left)
    (b : (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField →+*
      (orderedFamilyConfigurationOver f n).left.residueField z)
    (hb : Spec.map (CommRingCat.ofHom b) ≫
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) =
      (orderedFamilyConfigurationOver f n).left.fromSpecResidueField z ≫
        projectiveConfigurationQuotientMap 𝒜 f n) :
    (orderedFamilyConfigurationOver f n).left.fromSpecResidueField z ≫
        (orderedFamilyConfigurationOver f n).hom =
      Spec.map (CommRingCat.ofHom (b.comp a.hom)) := by
  let r := (orderedFamilyConfigurationOver f n).left.fromSpecResidueField z
  let q := projectiveConfigurationQuotientMap 𝒜 f n
  let g := (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
    (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
  let t := projectiveConfigurationQuotientToBase 𝒜 f n
  calc
    r ≫ (orderedFamilyConfigurationOver f n).hom = r ≫ (q ≫ t) :=
      congrArg (fun k => r ≫ k) (projectiveConfigurationQuotientMap_toBase 𝒜 f n).symm
    _ = (r ≫ q) ≫ t := (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom b) ≫ g) ≫ t :=
      congrArg (fun k => k ≫ t) hb.symm
    _ = Spec.map (CommRingCat.ofHom b) ≫ (g ≫ t) := Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom b) ≫ Spec.map a :=
      congrArg (fun k => Spec.map (CommRingCat.ofHom b) ≫ k) ha.symm
    _ = Spec.map (CommRingCat.ofHom (b.comp a.hom)) := by
      rw [← Spec.map_comp]
      rfl

/-- The ordered residue-field lift used for the generic cubic configuration
lies over the composite of the ground-field embedding with the induced
function-field embedding. -/
lemma quadraticOrderedLift_toBase
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
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
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField)) :
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    O.fromSpecResidueField z ≫
        (orderedFamilyConfigurationOver
          (hypersurfaceToBase cubic hcubic) 8).hom =
      Spec.map (CommRingCat.ofHom (b.comp a.hom)) := by
  dsimp only
  exact @projectiveConfigurationOrderedLift_toBase
    K (CoordinateRing (equationIdeal cubic hcubic)) _ _ _
    (grading (equationIdeal cubic hcubic)) _
    (hypersurfaceToBase cubic hcubic) 8 hsep hint a ha z
    (quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz)
    (quadraticOrderedLiftFunctionFieldHom_spec cubic hcubic z hz)

/-- A field-valued incidence point described by its ambient and equation
projections is the point induced from the corresponding finite-incidence
pullback. -/
lemma projectiveUniversalFamilyPoint_eq_finiteIncidenceParameterMap
    {R : Type u} [CommRing R] {σ : Type} [Finite σ] {d : ℕ}
    {X T S : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (marked : ι → (X ⟶ Proj (homogeneousSubmodule σ R)))
    (frame : T ⟶ projectiveParameters R σ d) (i : ι)
    (r : S ⟶ X) (t : S ⟶ T) (hbase : r ≫ xBase = t ≫ tBase)
    (q : S ⟶ projectiveUniversalFamily R σ d)
    (hq : q ≫ projectiveUniversalIncidence R σ d =
      Limits.prod.lift (r ≫ marked i) (t ≫ frame)) :
    q ≫ projectiveUniversalIncidence R σ d =
      pullback.lift r t hbase ≫
        projectiveUniversalFiniteIncidenceParameterMap R σ d
          xBase tBase marked frame i := by
  rw [hq]
  apply Limits.prod.hom_ext
  · rw [Limits.prod.lift_fst, Category.assoc,
      projectiveUniversalFiniteIncidenceParameterMap_fst,
      ← Category.assoc, pullback.lift_fst]
  · rw [Limits.prod.lift_snd, Category.assoc,
      projectiveUniversalFiniteIncidenceParameterMap_snd,
      ← Category.assoc, pullback.lift_snd]

/-- A normalized polynomial value remains normalized after applying an
algebra homomorphism to all coordinates. -/
lemma eval₂_algebraHom_eq_one_of_eq_one
    {K A L : Type u} [CommRing K] [CommRing A] [CommRing L]
    [Algebra K A] [Algebra K L]
    (φ : A →ₐ[K] L) {σ : Type} [Finite σ]
    (x : σ → A) (p : MvPolynomial σ K)
    (hp : p.eval₂ (algebraMap K A) x = 1) :
    p.eval₂ (algebraMap K L) (fun j => φ (x j)) = 1 := by
  have heval := MvPolynomial.hom_eval₂ p (algebraMap K A) φ.toRingHom x
  have hcomp : φ.toRingHom.comp (algebraMap K A) = algebraMap K L := by
    ext a
    exact φ.commutes a
  rw [hcomp] at heval
  calc
    p.eval₂ (algebraMap K L) (fun j => φ (x j)) =
        φ (p.eval₂ (algebraMap K A) x) := heval.symm
    _ = φ 1 := congrArg φ hp
    _ = 1 := map_one φ

/-- A linear combination of the original quadratic frame after scalar
extension is literally the same combination of the extended frame. -/
lemma quadraticEightFrameCombination_over_extension
    {K L : Type u} [Field K] [Field L]
    (f : K →+* L) (c : Fin 8 → L) :
    (∑ i, MvPolynomial.C (c i) * (quadraticEightFrame K i).1.map f) =
      (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 := by
  simp only [homogeneousFrameMap, Fintype.linearCombination_apply,
    Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [quadraticEightFrame_map f i]
  rw [MvPolynomial.smul_eq_C_mul]

/-- A scalar multiple of an extended-frame combination vanishes wherever
that combination vanishes. -/
lemma scaled_quadraticEightFrameCombination_evaluation_zero
    {K L E : Type u} [Field K] [Field L] [Field E] [Algebra L E]
    (f : K →+* L) (c : Fin 8 → L)
    (p : MvPolynomial (Fin 4) L) (α : L)
    (hp : p = MvPolynomial.C α *
      (∑ i, MvPolynomial.C (c i) * (quadraticEightFrame K i).1.map f))
    (x : Fin 4 → E)
    (hzero : MvPolynomial.eval₂ (algebraMap L E) x
      (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) :
    p.eval₂ (algebraMap L E) x = 0 := by
  rw [hp, quadraticEightFrameCombination_over_extension f c,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hzero, mul_zero]

/-- A coordinate algebra admits a four-coordinate presentation for which
quadratic restriction is surjective. -/
def HasSurjectiveQuadraticCoordinates
    (K A : Type u) [Field K] [CommRing A] [Algebra K A] : Prop :=
  ∃ x : Fin 4 → A,
    Function.Surjective (eval₂Hom (algebraMap K A) x) ∧
    Function.Surjective (homogeneousSectionRestriction (K := K) x 2)

/-- A coordinate algebra has an ambient presentation for which the quadrics
vanishing on it form a pencil. -/
def HasQuadraticPencilCoordinates
    (K A : Type u) [Field K] [CommRing A] [Algebra K A] : Prop :=
  ∃ x : Fin 4 → A,
    Function.Surjective (eval₂Hom (algebraMap K A) x) ∧
    finrank K (LinearMap.ker
      (homogeneousSectionRestriction (K := K) x 2)) = 2

/-- One normalized coordinate presentation together with the canonical
two-element basis of the full quadratic restriction kernel. -/
structure NormalizedQuadraticPencilBasisData
    (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    (p : MvPolynomial (Fin 4) K) where
  x : Fin 4 → A
  ell : MvPolynomial (Fin 4) K
  evalSurjective : Function.Surjective (eval₂Hom (algebraMap K A) x)
  ellHomogeneous : ell.IsHomogeneous 1
  ellEvaluation : ell.eval₂ (algebraMap K A) x = 1
  cubicEvaluation : p.eval₂ (algebraMap K A) x = 0
  kernelFinrank : Module.finrank K (LinearMap.ker
    (homogeneousSectionRestriction (K := K) x 2)) = 2
  basisData : ∀ i : Fin 2,
    ((quadraticVanishingPencilBasis x kernelFinrank i).1.1).IsHomogeneous 2 ∧
      (quadraticVanishingPencilBasis x kernelFinrank i).1.1.eval₂
        (algebraMap K A) x = 0

/-- A coordinate presentation whose eight labeled evaluations detect the
canonical quadratic frame. -/
structure DetectingQuadraticEightFrameCoordinates
    (K A L : Type u) [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L) where
  ell : MvPolynomial (Fin 4) K
  ellHomogeneous : ell.IsHomogeneous 1
  x : Fin 4 → A
  evalSurjective : Function.Surjective (eval₂Hom (algebraMap K A) x)
  detects : ∀ c : Fin 8 → K,
    (∀ i, MvPolynomial.eval₂ (algebraMap K L)
      (fun j => φ i (x j))
      (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
    c = 0

/-- Eight detecting algebra maps give surjective quadratic coordinates on a
rank-eight algebra. -/
theorem hasSurjectiveQuadraticCoordinates_of_embedding_evaluations
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A)
    (hx : Function.Surjective (eval₂Hom (algebraMap K A) x))
    (hA : finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hdetect : ∀ c : Fin 8 → K,
      (∀ i, MvPolynomial.eval₂ (algebraMap K L)
        (fun j => φ i (x j))
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0) :
    HasSurjectiveQuadraticCoordinates K A :=
  ⟨x, hx, quadraticSectionRestriction_surjective_of_embedding_evaluations
    x hA φ hdetect⟩

/-- A normalized detecting presentation packages the normalization, the
cubic equation, and the canonical basis of its two-dimensional quadratic
kernel. -/
noncomputable def normalizedQuadraticPencilBasisData_of_embedding_evaluations
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K)
    (x : Fin 4 → A) (ell : MvPolynomial (Fin 4) K)
    (hx : Function.Surjective (eval₂Hom (algebraMap K A) x))
    (hell : ell.IsHomogeneous 1)
    (hxell : ell.eval₂ (algebraMap K A) x = 1)
    (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hA : finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hdetect : ∀ c : Fin 8 → K,
      (∀ i, MvPolynomial.eval₂ (algebraMap K L)
        (fun j => φ i (x j))
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0) :
    NormalizedQuadraticPencilBasisData K A p := by
  have hquad := quadraticSectionRestriction_surjective_of_embedding_evaluations
    x hA φ hdetect
  let hker :=
    quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
      x hA hquad
  exact {
    x := x
    ell := ell
    evalSurjective := hx
    ellHomogeneous := hell
    ellEvaluation := hxell
    cubicEvaluation := hpx
    kernelFinrank := hker
    basisData := quadraticVanishingPencilBasis_data x hker }

/-- Surjective quadratic coordinates on a rank-eight algebra exhibit the
quadrics vanishing on it as a two-dimensional pencil, while retaining the
same surjective ambient coordinate presentation. -/
theorem HasSurjectiveQuadraticCoordinates.exists_kernel_finrank_eq_two
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (hA : finrank K A = 8)
    (h : HasSurjectiveQuadraticCoordinates K A) :
    HasQuadraticPencilCoordinates K A := by
  unfold HasQuadraticPencilCoordinates
  obtain ⟨x, hx, hquad⟩ := h
  exact ⟨x, hx,
    quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
      x hA hquad⟩

/-- Surjective quadratic coordinates on a rank-eight algebra provide the
full two-generator pencil, with homogeneity and vanishing recorded for both
generators.  This is the finite presentation used by the direct
determinantal route to generic regularity. -/
theorem HasSurjectiveQuadraticCoordinates.exists_pencilBasis_data
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (hA : finrank K A = 8)
    (h : HasSurjectiveQuadraticCoordinates K A) :
    ∃ (x : Fin 4 → A)
      (hx : Function.Surjective (eval₂Hom (algebraMap K A) x))
      (hker : finrank K (LinearMap.ker
        (homogeneousSectionRestriction (K := K) x 2)) = 2),
      ∀ i : Fin 2,
        ((quadraticVanishingPencilBasis x hker i).1.1).IsHomogeneous 2 ∧
          (quadraticVanishingPencilBasis x hker i).1.1.eval₂
            (algebraMap K A) x = 0 := by
  obtain ⟨x, hx, hquad⟩ := h
  let hker :=
    quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
      x hA hquad
  exact ⟨x, hx, hker, quadraticVanishingPencilBasis_data x hker⟩

/-- A vanishing equation on coordinates obtained from a normalized finite
chart supplies an exact universal-incidence point, with externally specified
ambient and equation projections. -/
theorem exists_projectiveUniversalFamily_point_of_mappedNormalized_evaluation_zero
    {K Q A L : Type u} [Field K] [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    (a : K →+* Q)
    {d : ℕ} (p : MvPolynomial (Fin 4) Q) (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    (x : Fin 4 → A)
    (he : ∀ q ∈ (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q)).toIdeal,
      (eval₂Hom (algebraMap Q A) x) q = 0)
    (ell : MvPolynomial (Fin 4) Q) (hell : ell.IsHomogeneous 1)
    (hellOne : (Ideal.Quotient.lift
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)).toIdeal
      (eval₂Hom (algebraMap Q A) x) he)
        (Ideal.Quotient.mk
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q)).toIdeal ell) = 1)
    (φ : A →ₐ[Q] L)
    (hzero : p.eval₂ (algebraMap Q L) (fun j => φ (x j)) = 0)
    {X T : Scheme.{u}} {ι : Type} (i : ι)
    (r : Spec (.of L) ⟶ X)
    (marked : ι → (X ⟶ Proj (homogeneousSubmodule (Fin 4) K)))
    (t : Spec (.of L) ⟶ T)
    (frame : T ⟶ projectiveParameters K (Fin 4) d)
    (hambient : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
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
        ambientCoefficientMap a = r ≫ marked i)
    (hequation : Spec.map (CommRingCat.ofHom (algebraMap Q L)) ≫
        projectiveClassifyingMap p hp hne a = t ≫ frame) :
    ∃ u : Spec (.of L) ⟶ projectiveUniversalFamily K (Fin 4) d,
      u ≫ projectiveUniversalIncidence K (Fin 4) d =
        Limits.prod.lift (r ≫ marked i) (t ≫ frame) := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q) := ⊥
  let xL : Fin 4 → L := fun j => φ (x j)
  let heL : ∀ q ∈ I.toIdeal,
      (eval₂Hom (algebraMap Q L) xL) q = 0 := by
    intro q hq
    exact (Ideal.mem_bot.mp hq).symm ▸ map_zero _
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal ell
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  have hellEval : ell.eval₂ (algebraMap Q A) x = 1 := by
    exact hellOne
  have hzOneL : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap Q L) xL) heL) z = 1 := by
    change ell.eval₂ (algebraMap Q L) (fun j => φ (x j)) = 1
    exact eval₂_algebraHom_eq_one_of_eq_one φ x ell hellEval
  obtain ⟨u, hu⟩ :=
    exists_projectiveUniversalFamily_point_of_linearNormalized_evaluation_zero
      a p hp hne xL heL z hz hzOneL hzero
  refine ⟨u, hu.trans ?_⟩
  apply Limits.prod.hom_ext
  · rw [Limits.prod.lift_fst, Limits.prod.lift_fst]
    have hnat := linearNormalizedPointAt_naturality I x he φ xL
      (fun _ => rfl) heL z hz hellOne hzOneL
    calc
      linearNormalizedPointAt I xL heL z hz hzOneL ≫
          (quotientProjMap I ≫ ambientCoefficientMap a) =
        (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
            linearNormalizedPointAt I x he z hz hellOne) ≫
          (quotientProjMap I ≫ ambientCoefficientMap a) :=
        congrArg (fun k => k ≫
          (quotientProjMap I ≫ ambientCoefficientMap a)) hnat
      _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          (linearNormalizedPointAt I x he z hz hellOne ≫
            (quotientProjMap I ≫ ambientCoefficientMap a)) :=
        Category.assoc _ _ _
      _ = r ≫ marked i := by simpa only [I, z] using hambient
  · rw [Limits.prod.lift_snd, Limits.prod.lift_snd]
    exact hequation

/-- A single normalized homogeneous equation which vanishes after every marked
component evaluation supplies simultaneous universal-incidence lifts.  The
conclusion is stated in the exact pullback form consumed by the finite
incidence bad-locus API. -/
theorem exists_common_projectiveUniversalFamily_points_of_normalized_evaluation_zero
    {K Q A L : Type u} [Field K] [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    (a : K →+* Q)
    {d : ℕ} (p : MvPolynomial (Fin 4) Q) (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    (x : Fin 4 → A)
    (he : ∀ q ∈ (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q)).toIdeal,
      (eval₂Hom (algebraMap Q A) x) q = 0)
    (ell : MvPolynomial (Fin 4) Q) (hell : ell.IsHomogeneous 1)
    (hellOne : (Ideal.Quotient.lift
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)).toIdeal
      (eval₂Hom (algebraMap Q A) x) he)
        (Ideal.Quotient.mk
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q)).toIdeal ell) = 1)
    {X T : Scheme.{u}} {n : ℕ}
    (xBase : X ⟶ Spec (.of K))
    (r : Spec (.of L) ⟶ X)
    (marked : Fin n → (X ⟶ Proj (homogeneousSubmodule (Fin 4) K)))
    (t : Spec (.of L) ⟶ T)
    (tBase : T ⟶ Spec (.of K))
    (frame : T ⟶ projectiveParameters K (Fin 4) d)
    (hbase : r ≫ xBase = t ≫ tBase)
    (φ : Fin n → A →ₐ[Q] L)
    (hzero : ∀ i, p.eval₂ (algebraMap Q L) (fun j => φ i (x j)) = 0)
    (hambient : ∀ i,
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
          ambientCoefficientMap a = r ≫ marked i)
    (hequation : Spec.map (CommRingCat.ofHom (algebraMap Q L)) ≫
        projectiveClassifyingMap p hp hne a = t ≫ frame) :
    ∃ q : Fin n → (Spec (.of L) ⟶
        projectiveUniversalFamily K (Fin 4) d),
      ∀ i, q i ≫ projectiveUniversalIncidence K (Fin 4) d =
        pullback.lift r t hbase ≫
          projectiveUniversalFiniteIncidenceParameterMap K (Fin 4) d
            xBase tBase marked frame i := by
  have hexists : ∀ i, ∃ u : Spec (.of L) ⟶
      projectiveUniversalFamily K (Fin 4) d,
      u ≫ projectiveUniversalIncidence K (Fin 4) d =
        Limits.prod.lift (r ≫ marked i) (t ≫ frame) := by
    intro i
    exact exists_projectiveUniversalFamily_point_of_mappedNormalized_evaluation_zero
      a p hp hne x he ell hell hellOne (φ i) (hzero i) i r marked t frame
        (hambient i) hequation
  let q : Fin n → (Spec (.of L) ⟶
      projectiveUniversalFamily K (Fin 4) d) := fun i => (hexists i).choose
  refine ⟨q, ?_⟩
  intro i
  exact projectiveUniversalFamilyPoint_eq_finiteIncidenceParameterMap
    xBase tBase marked frame i r t hbase (q i) (hexists i).choose_spec

/-- The simultaneous lifts from the preceding theorem place the chosen field
point in the universal finite-incidence bad locus. -/
theorem mem_projectiveUniversalFiniteIncidenceBadLocus_of_normalized_evaluation_zero
    {K Q A L : Type u} [Field K] [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    (a : K →+* Q)
    {d : ℕ} (p : MvPolynomial (Fin 4) Q) (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    (x : Fin 4 → A)
    (he : ∀ q ∈ (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q)).toIdeal,
      (eval₂Hom (algebraMap Q A) x) q = 0)
    (ell : MvPolynomial (Fin 4) Q) (hell : ell.IsHomogeneous 1)
    (hellOne : (Ideal.Quotient.lift
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)).toIdeal
      (eval₂Hom (algebraMap Q A) x) he)
        (Ideal.Quotient.mk
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q)).toIdeal ell) = 1)
    {X T : Scheme.{u}} {n : ℕ}
    (xBase : X ⟶ Spec (.of K))
    (r : Spec (.of L) ⟶ X)
    (marked : Fin n → (X ⟶ Proj (homogeneousSubmodule (Fin 4) K)))
    (t : Spec (.of L) ⟶ T)
    (tBase : T ⟶ Spec (.of K))
    (frame : T ⟶ projectiveParameters K (Fin 4) d)
    (hbase : r ≫ xBase = t ≫ tBase)
    (φ : Fin n → A →ₐ[Q] L)
    (hzero : ∀ i, p.eval₂ (algebraMap Q L) (fun j => φ i (x j)) = 0)
    (hambient : ∀ i,
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
          ambientCoefficientMap a = r ≫ marked i)
    (hequation : Spec.map (CommRingCat.ofHom (algebraMap Q L)) ≫
        projectiveClassifyingMap p hp hne a = t ≫ frame) :
    r (IsLocalRing.closedPoint L) ∈
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        xBase tBase marked frame := by
  obtain ⟨q, hq⟩ :=
    exists_common_projectiveUniversalFamily_points_of_normalized_evaluation_zero
      a p hp hne x he ell hell hellOne xBase r marked t tBase frame hbase
        φ hzero hambient hequation
  exact mem_projectiveUniversalFiniteIncidenceBadLocus_of_common_fieldPoints
    K (Fin 4) d xBase tBase marked frame r t hbase q hq

/-- Polynomial vanishing in a coefficient algebra remains vanishing after
applying any algebra homomorphism.  This is the componentwise transport used
for an ordered residue-field realization of a finite scheme. -/
theorem eval₂_algHom_eq_zero_of_eval₂_eq_zero
    {Q A L : Type u} [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    (p : MvPolynomial (Fin 4) Q) (x : Fin 4 → A)
    (φ : A →ₐ[Q] L)
    (hzero : p.eval₂ (algebraMap Q A) x = 0) :
    p.eval₂ (algebraMap Q L) (fun j => φ (x j)) = 0 := by
  have hcomp : φ.toRingHom.comp (algebraMap Q A) = algebraMap Q L := by
    ext q
    exact φ.commutes q
  calc
    p.eval₂ (algebraMap Q L) (fun j => φ (x j)) =
        φ (p.eval₂ (algebraMap Q A) x) := by
      rw [← hcomp]
      exact (hom_eval₂ p (algebraMap Q A) φ.toRingHom x).symm
    _ = 0 := by rw [hzero, map_zero]

/-- A nonzero quadratic-frame vector over an intermediate field gives a
residue-field parameter whose base map is the composite of the two field
embeddings and whose equation is the retained scalar multiple. -/
theorem exists_quadraticEightFrame_residueParameter_of_nonzero
    {K Q L : Type u} [Field K] [Field Q] [Field L]
    (a : K →+* Q) (b : Q →+* L)
    (rBase : Spec (.of L) ⟶ Spec (.of K))
    (hrBase : rBase = Spec.map (CommRingCat.ofHom (b.comp a)))
    (c : Fin 8 → Q) (hc : c ≠ 0) :
    ∃ (t : Spec (.of L) ⟶
        projectiveLinearSystemParameters (K := K) (τ := Fin 8))
      (p : MvPolynomial (Fin 4) Q) (hp : p.IsHomogeneous 2) (hne : p ≠ 0)
      (α : Q),
      α ≠ 0 ∧
      p = MvPolynomial.C α *
        (∑ j, MvPolynomial.C (c j) * (quadraticEightFrame K j).1.map a) ∧
      rBase = t ≫ toBase
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K)) ∧
      Spec.map (CommRingCat.ofHom b) ≫
          projectiveClassifyingMap p hp hne a =
        t ≫ homogeneousFrameToParameters 2
          ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
          (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K) := by
  obtain ⟨tQ, p, hp, hne, α, hα, hpScale, htQBase, htQClass⟩ :=
    exists_homogeneousFrame_parameter_of_nonzero_coordinates
      a ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
      (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K) c hc
  let t := Spec.map (CommRingCat.ofHom b) ≫ tQ
  have htBase : rBase = t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K)) := by
    calc
      rBase = Spec.map (CommRingCat.ofHom (b.comp a)) := hrBase
      _ = Spec.map (CommRingCat.ofHom b) ≫
          Spec.map (CommRingCat.ofHom a) := by
        rw [← Spec.map_comp]
        rfl
      _ = Spec.map (CommRingCat.ofHom b) ≫
          (tQ ≫ toBase
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 8) K))) :=
        congrArg (fun k => Spec.map (CommRingCat.ofHom b) ≫ k) htQBase.symm
      _ = t ≫ toBase
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K)) :=
        (Category.assoc _ _ _).symm
  have htClass : Spec.map (CommRingCat.ofHom b) ≫
        projectiveClassifyingMap p hp hne a =
      t ≫ homogeneousFrameToParameters 2
        ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
        (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K) := by
    calc
      Spec.map (CommRingCat.ofHom b) ≫
          projectiveClassifyingMap p hp hne a =
        Spec.map (CommRingCat.ofHom b) ≫
          (tQ ≫ homogeneousFrameToParameters 2
            ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
            (quadraticEightFrame K)
            (quadraticEightFrame_linearIndependent K)) :=
        congrArg (fun k => Spec.map (CommRingCat.ofHom b) ≫ k) htQClass.symm
      _ = t ≫ homogeneousFrameToParameters 2
          ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
          (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K) :=
        (Category.assoc _ _ _).symm
  exact ⟨t, p, hp, hne, α, hα, hpScale, htBase, htClass⟩

/-- Incidence avoidance detects every coefficient vector in the quadratic
frame once normalized coordinates evaluate at the marked points. -/
theorem quadraticEightFrame_detected_of_noCommonIncidence
    {K Q A L : Type u} [Field K] [Field Q] [CommRing A] [Field L]
    [Algebra Q A] [Algebra Q L]
    (a : K →+* Q) (b : Q →+* L) (hb : algebraMap Q L = b)
    {X : Scheme.{u}}
    (xBase : X ⟶ Spec (.of K))
    (marked : Fin 8 → (X ⟶ Proj (homogeneousSubmodule (Fin 4) K)))
    (r : Spec (.of L) ⟶ X)
    (hrBase : r ≫ xBase = Spec.map (CommRingCat.ofHom (b.comp a)))
    (x : Fin 4 → A)
    (he : ∀ q ∈ (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q)).toIdeal,
      (eval₂Hom (algebraMap Q A) x) q = 0)
    (ell : MvPolynomial (Fin 4) Q) (hell : ell.IsHomogeneous 1)
    (hellOne : (Ideal.Quotient.lift
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)).toIdeal
      (eval₂Hom (algebraMap Q A) x) he)
        (Ideal.Quotient.mk
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q)).toIdeal ell) = 1)
    (φ : Fin 8 → A →ₐ[Q] L)
    (hmarked : ∀ i,
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
          ambientCoefficientMap a = r ≫ marked i)
    (hno : ¬ ∃ (t : Spec (.of L) ⟶
        projectiveLinearSystemParameters (K := K) (τ := Fin 8))
      (q : Fin 8 → (Spec (.of L) ⟶
        projectiveUniversalFamily K (Fin 4) 2))
      (hbase : r ≫ xBase = t ≫ toBase
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K))),
      ∀ i, q i ≫ projectiveUniversalIncidence K (Fin 4) 2 =
        pullback.lift r t hbase ≫
          projectiveUniversalFiniteIncidenceParameterMap K (Fin 4) 2
            xBase
            (toBase
              (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K)))
            marked
            (homogeneousFrameToParameters 2
              ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
              (quadraticEightFrame K)
              (quadraticEightFrame_linearIndependent K)) i) :
    ∀ c : Fin 8 → Q,
      (∀ i, MvPolynomial.eval₂ (algebraMap Q L)
        (fun j => φ i (x j))
        (homogeneousFrameMap 2 (quadraticEightFrame Q) c).1 = 0) →
      c = 0 := by
  intro c hzero
  by_contra hc
  obtain ⟨t, p, hp, hne, α, hα, hpScale, htBase, htClass⟩ :=
    exists_quadraticEightFrame_residueParameter_of_nonzero
      a b (r ≫ xBase) hrBase c hc
  have hexists : ∀ i, ∃ u : Spec (.of L) ⟶
      projectiveUniversalFamily K (Fin 4) 2,
      u ≫ projectiveUniversalIncidence K (Fin 4) 2 =
        Limits.prod.lift (r ≫ marked i)
          (t ≫ homogeneousFrameToParameters 2
            ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
            (quadraticEightFrame K)
            (quadraticEightFrame_linearIndependent K)) := by
    intro i
    have hpzero : p.eval₂ (algebraMap Q L) (fun j => φ i (x j)) = 0 :=
      scaled_quadraticEightFrameCombination_evaluation_zero
        a c p α hpScale (fun j => φ i (x j)) (hzero i)
    apply exists_projectiveUniversalFamily_point_of_mappedNormalized_evaluation_zero
      a p hp hne x he ell hell hellOne (φ i) hpzero i r marked t
      (homogeneousFrameToParameters 2
        ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
        (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K))
      (hmarked i)
    simpa only [hb] using htClass
  let q : Fin 8 → (Spec (.of L) ⟶
      projectiveUniversalFamily K (Fin 4) 2) := fun i => (hexists i).choose
  have hq : ∀ i, q i ≫ projectiveUniversalIncidence K (Fin 4) 2 =
      Limits.prod.lift (r ≫ marked i)
        (t ≫ homogeneousFrameToParameters 2
          ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
          (quadraticEightFrame K)
          (quadraticEightFrame_linearIndependent K)) := fun i => (hexists i).choose_spec
  apply hno
  refine ⟨t, q, htBase, ?_⟩
  intro i
  exact projectiveUniversalFamilyPoint_eq_finiteIncidenceParameterMap
    xBase
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K)))
    marked
    (homogeneousFrameToParameters 2
      ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
      (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K))
    i r t htBase (q i) (hq i)

/-- A normalized ambient chart on the coefficient-changed generic scheme
evaluates under every labeled component map at the corresponding ordered
marked point. -/
theorem quadraticOrderedLift_normalizedAmbientChart_toMarkedPoint
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
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
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField)) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
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
      ∀ i,
        Spec.map (CommRingCat.ofHom
            (quadraticOrderedLiftCoefficientChangedComponentAlgHom
              cubic hcubic a ha z hz i).toRingHom) ≫
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
          ambientCoefficientMap a.hom =
        O.fromSpecResidueField z ≫
          @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal cubic hcubic)) _
            (hypersurfaceToBase cubic hcubic) hsep 8
            (hypersurfaceToAmbient cubic hcubic) i := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField
      ((orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).left.residueField z) := b.toAlgebra
  intro ell hell x he hellOne hpoint i
  let c := linearNormalizedPointAt
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
      hypersurfaceToAmbient p' hp' ≫ ambientCoefficientMap a.hom := by
    exact (congrArg (fun k => k ≫ ambientCoefficientMap a.hom) hpoint).trans
      (Category.assoc _ _ _)
  exact quadraticOrderedLiftCoefficientChangedComponentAlgHom_chart_toMarkedPoint
    cubic hcubic a ha z hz i c hc

/-- On a normalized ambient chart of the coefficient-changed generic
rank-eight scheme, the ordered incidence-avoidance hypothesis detects every
coefficient vector in the canonical quadratic frame. -/
theorem quadraticOrderedLift_normalizedAmbientChart_detects
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
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
    (hno : QuadraticEightNoCommonResidueFieldEquationAt cubic hcubic z) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
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
      ∀ c : Fin 8 → Q.functionField,
        (∀ i, MvPolynomial.eval₂
          (algebraMap Q.functionField (O.residueField z))
          (fun j => φ i (x j))
          (homogeneousFrameMap 2 (quadraticEightFrame Q.functionField) c).1 = 0) →
        c = 0 := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
    fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
      cubic hcubic a ha z hz i
  intro ell hell x he hellOne hpoint
  let r := O.fromSpecResidueField z
  let marked : Fin 8 →
      (O ⟶ Proj (homogeneousSubmodule (Fin 4) K)) := fun i =>
    @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _
      (hypersurfaceToBase cubic hcubic) hsep 8
      (hypersurfaceToAmbient cubic hcubic) i
  have hrBase : r ≫ (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).hom =
      Spec.map (CommRingCat.ofHom (b.comp a.hom)) := by
    let f : Proj (grading (equationIdeal cubic hcubic)) ⟶ Spec (.of K) :=
      toBase (equationIdeal cubic hcubic)
    letI : IsSeparated f := hsep
    letI : IsIntegral
        (projectiveConfigurationQuotientOpen
          (grading (equationIdeal cubic hcubic)) f 8).toScheme := hint
    have ha' : Spec.map a =
        (projectiveConfigurationQuotientOpen
          (grading (equationIdeal cubic hcubic)) f 8).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen
              (grading (equationIdeal cubic hcubic)) f 8).toScheme) ≫
          projectiveConfigurationQuotientToBase
            (grading (equationIdeal cubic hcubic)) f 8 := by
      exact ha
    have hb' : Spec.map (CommRingCat.ofHom b) ≫
        (projectiveConfigurationQuotientOpen
          (grading (equationIdeal cubic hcubic)) f 8).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen
              (grading (equationIdeal cubic hcubic)) f 8).toScheme) =
        (orderedFamilyConfigurationOver f 8).left.fromSpecResidueField z ≫
          projectiveConfigurationQuotientMap
            (grading (equationIdeal cubic hcubic)) f 8 := by
      exact quadraticOrderedLiftFunctionFieldHom_spec cubic hcubic z hz
    exact @projectiveConfigurationOrderedLift_toBase
      K (CoordinateRing (equationIdeal cubic hcubic)) _ _ _
      (grading (equationIdeal cubic hcubic)) _
      f 8 hsep hint a ha' z b hb'
  have hmarked := quadraticOrderedLift_normalizedAmbientChart_toMarkedPoint
    cubic hcubic a ha z hz ell hell x he hellOne hpoint
  apply quadraticEightFrame_detected_of_noCommonIncidence
    a.hom b rfl
    (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).hom
    marked r hrBase x he ell hell hellOne φ hmarked
  exact hno

/-- The ordered generic length-eight scheme admits normalized coordinates
whose eight labeled component evaluations detect the canonical quadratic
frame. -/
theorem exists_cubicConfigurationGenericEight_detectingCoordinates_of_noCommon
    {K : Type u} [Field K]
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
    (hno : QuadraticEightNoCommonResidueFieldEquationAt cubic hcubic z) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    Nonempty (DetectingQuadraticEightFrameCoordinates
      Q.functionField Γ(D.val.subscheme, ⊤) (O.residueField z) φ) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p' hp') := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  obtain ⟨ell, hell, x, he, hellOne, hxsurj, _, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_ambient_chart p' hp' D.val.subschemeι
  refine ⟨{
    ell := ell
    ellHomogeneous := hell
    x := x
    evalSurjective := hxsurj
    detects := ?_ }⟩
  exact quadraticOrderedLift_normalizedAmbientChart_detects
    cubic hcubic a ha z hz hno ell hell x he hellOne hpoint

/-- The incidence argument can be retained in the particular normalized
chart from which it is proved.  In that same chart the full quadratic
restriction kernel has an explicit two-element basis. -/
theorem cubicConfigurationGenericEight_normalizedQuadraticPencilBasis_of_noCommon
    {K : Type u} [Field K]
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
    (hno : QuadraticEightNoCommonResidueFieldEquationAt cubic hcubic z) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p' hp') := D.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D.val.subschemeι ≫ hypersurfaceToBase p' hp')
    Nonempty (NormalizedQuadraticPencilBasisData
      Q.functionField Γ(D.val.subscheme, ⊤) p') := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p' hp') := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p' hp')
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p' hp')
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D.val.subschemeι ≫ hypersurfaceToBase p' hp')
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
    fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
      cubic hcubic a ha z hz i
  obtain ⟨ell, hell, x, he, hellOne, hxsurj, hpvan, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_ambient_chart p' hp' D.val.subschemeι
  have hdetect : ∀ c : Fin 8 → Q.functionField,
      (∀ i, MvPolynomial.eval₂ (algebraMap Q.functionField (O.residueField z))
        (fun j => φ i (x j))
        (homogeneousFrameMap 2 (quadraticEightFrame Q.functionField) c).1 = 0) →
      c = 0 :=
    quadraticOrderedLift_normalizedAmbientChart_detects
      cubic hcubic a ha z hz hno ell hell x he hellOne hpoint
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 8 := by
    apply (finiteSchemeCoefficient_finrank
      (D.val.subschemeι ≫ hypersurfaceToBase p' hp')).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint Q.functionField)
  have hxell : ell.eval₂
      (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 1 := by
    change (eval₂Hom
      (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) ell = 1
    simp only [Ideal.Quotient.lift_mk] at hellOne
    convert hellOne using 1
  exact ⟨normalizedQuadraticPencilBasisData_of_embedding_evaluations
    p' x ell hxsurj hell hxell hpvan hA φ hdetect⟩

/-- Incidence avoidance for the ordered generic configuration implies that
quadratic sections restrict surjectively to the actual coefficient-changed
generic length-eight scheme. -/
theorem exists_cubicConfigurationGenericEight_quadraticRestriction_surjective_of_noCommon
    {K : Type u} [Field K]
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
    (hno : QuadraticEightNoCommonResidueFieldEquationAt cubic hcubic z) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    HasSurjectiveQuadraticCoordinates
      Q.functionField Γ(D.val.subscheme, ⊤) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
    fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
      cubic hcubic a ha z hz i
  obtain ⟨detection⟩ :=
    exists_cubicConfigurationGenericEight_detectingCoordinates_of_noCommon
      cubic hcubic a ha z hz hno
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 8 := by
    apply (finiteSchemeCoefficient_finrank pD).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint Q.functionField)
  exact hasSurjectiveQuadraticCoordinates_of_embedding_evaluations
    detection.x detection.evalSurjective hA φ detection.detects

/-- For a prime cubic over an algebraically closed field, the generic
length-eight configuration has surjective quadratic restriction: choose the
ordered lift outside the universal incidence locus and apply the preceding
detection theorem. -/
theorem cubicConfigurationGenericEight_hasSurjectiveQuadraticCoordinates
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span
      ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    [Infinite (cubicConfigurationBase cubic hcubic 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
      cubicConfigurationToBase cubic hcubic 8) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    HasSurjectiveQuadraticCoordinates
      Q.functionField Γ(D.val.subscheme, ⊤) := by
  dsimp only
  obtain ⟨z, hz, hno⟩ :=
    exists_orderedPointOver_genericEight_with_noCommonQuadraticEightEquation
      cubic hcubic hcubic_ne hcubic_prime
  exact exists_cubicConfigurationGenericEight_quadraticRestriction_surjective_of_noCommon
    cubic hcubic a ha z hz hno


end PfaffianDescent

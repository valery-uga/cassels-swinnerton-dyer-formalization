import PfaffianDescent.VoisinGenericEightEvaluationDirect
import PfaffianDescent.VoisinProjectiveVectorSchemePoint
import AllCharacteristics.OrderedConfigurationFieldPoints
import AllCharacteristics.VoisinGenericCubicConfiguration
import AllCharacteristics.ProjectiveConfigurationFieldPointSplitFiber
import PfaffianDescent.VoisinFiniteAlgebraRationalPointSplit

/-!
# Eight projective vectors as an ordered cubic-surface configuration

A finite tuple of nonzero, projectively distinct vector zeros of a cubic
defines an actual field-valued point of its ordered configuration space.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicVector_zero_equationIdeal
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (v : Fin 4 → L) (hv : p.eval v = 0) :
    ∀ f ∈ (equationIdeal p hp).toIdeal, f.eval v = 0 := by
  intro f hf
  change f ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) L)) at hf
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hf
  rw [hg, MvPolynomial.eval_mul, hv, zero_mul]

theorem exists_ordered_eight_configuration_of_cubic_vectors
    {L : Type u} [Field L] [Infinite L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (y : Fin 8 → Fin 4 → L)
    (hzero : ∀ i, p.eval (y i) = 0)
    (hnonzero : ∀ i, y i ≠ 0)
    (hprojective : ∀ i j, i ≠ j → ∀ c : L, c • y i ≠ y j) :
    ∃ (c : Fin 4 → L)
      (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0),
      ∃ (q : Fin 8 → (Spec (.of L) ⟶ hypersurface p hp))
        (A : Spec (.of L) ⟶
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left),
        (∀ i, q i = projectiveVectorSchemePointInLinearChart
          (equationIdeal p hp) c (y i)
          (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)) ∧
        Function.Injective q ∧
        A ≫ (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom =
            Spec.map (CommRingCat.ofHom (RingHom.id L)) ∧
        (∀ i, (A ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left = q i) := by
  obtain ⟨c, hc⟩ := exists_common_linear_chart_for_nonzero_vectors y hnonzero
  let q : Fin 8 → (Spec (.of L) ⟶ hypersurface p hp) := fun i =>
    projectiveVectorSchemePointInLinearChart (equationIdeal p hp) c (y i)
      (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)
  have hbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    intro i
    exact projectiveVectorSchemePointInLinearChart_toBase
      (equationIdeal p hp) c (y i)
      (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)
  have hqinj : Function.Injective q := by
    intro i j hij
    by_contra hne
    exact (projectiveVectorSchemePointInLinearChart_ne_of_directions
      (equationIdeal p hp) c
      (cubicVector_zero_equationIdeal p hp (y i) (hzero i))
      (cubicVector_zero_equationIdeal p hp (y j) (hzero j))
      (hc i) (hc j) (hprojective i j hne)) hij
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    @IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase p hp)
  obtain ⟨A, hA, hcoords⟩ :=
    exists_orderedConfigurationFieldPoint
      (hypersurfaceToBase p hp) 8
      (Spec.map (CommRingCat.ofHom (RingHom.id L))) q hbase
      (fun i j hij => hqinj.ne hij)
  exact ⟨c, hc, q, A, (fun _ => rfl), hqinj, hA, hcoords⟩

/-- Eight nonzero, pairwise projectively distinct vector zeros of an
arbitrary cubic determine both an ordered configuration point and its
associated split finite étale degree-eight subscheme. -/
theorem exists_ordered_eight_finite_datum_of_cubic_vectors
    {L : Type u} [Field L] [Infinite L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (y : Fin 8 → Fin 4 → L)
    (hzero : ∀ i, p.eval (y i) = 0)
    (hnonzero : ∀ i, y i ≠ 0)
    (hprojective : ∀ i j, i ≠ j → ∀ c : L, c • y i ≠ y j) :
    ∃ (c : Fin 4 → L)
      (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
      (q : Fin 8 → (Spec (.of L) ⟶ hypersurface p hp))
      (A : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
      (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
      (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8),
      (∀ i, q i = projectiveVectorSchemePointInLinearChart
        (equationIdeal p hp) c (y i)
        (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)) ∧
      Function.Injective q ∧
      A ≫ (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom =
          Spec.map (CommRingCat.ofHom (RingHom.id L)) ∧
      A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B ∧
      B ≫ cubicConfigurationToBase p hp 8 =
        Spec.map (CommRingCat.ofHom (RingHom.id L)) ∧
      (∃ hB : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _,
        D = projectiveConfigurationFiniteSubschemeAt
          (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8 B hB) ∧
      Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      (∃ E : (∐ fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) ≅
          D.val.subscheme,
        ∀ i, Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
          (ULift.up i) ≫ E.hom ≫ D.val.subschemeι = q i) ∧
      (∀ i, (A ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left = q i) := by
  obtain ⟨c, hc, q, A, hq, hqinj, hA, hcoords⟩ :=
    exists_ordered_eight_configuration_of_cubic_vectors
      p hp y hzero hnonzero hprojective
  let B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8 :=
    A ≫ configurationQuotientMap (equationIdeal p hp) 8
  have hBbase : B ≫ cubicConfigurationToBase p hp 8 =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    let I := equationIdeal p hp
    have hrel := configurationQuotientMap_toBase I 8
    calc
      B ≫ cubicConfigurationToBase p hp 8 =
          A ≫ (configurationQuotientMap I 8 ≫
            configurationQuotientToBase I 8) := by
              exact Category.assoc _ _ _
      _ = A ≫ (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom :=
        congrArg (fun f => A ≫ f) hrel
      _ = _ := hA
  have hBid : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _ := by
    simpa using hBbase
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    @IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase p hp)
  have hsep' : IsSeparated (hypersurfaceToBase p hp) := inferInstance
  let D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8 :=
    projectiveConfigurationFiniteSubschemeAt
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8 B hBid
  have hDet : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) := by
    change Etale ((projectiveConfigurationFiniteSubschemeAt
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8 B hBid).val.subschemeι ≫
        hypersurfaceToBase p hp)
    exact @projectiveConfigurationFiniteSubschemeAt_toBase_etale
      _ _ _ _ _ (grading (equationIdeal p hp)) _ _ _
      (hypersurfaceToBase p hp) hsep' 8 B hBid
  let E : (∐ fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) ≅ D.val.subscheme :=
    @projectiveConfigurationFiniteSubschemeAtIsoConstantCover
      _ _ _ _ _ (grading (equationIdeal p hp)) _ _ _
      (hypersurfaceToBase p hp) hsep' 8 A hBid
  have hSplit : ∀ i,
      Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
        (ULift.up i) ≫ E.hom ≫ D.val.subschemeι = q i := by
    intro i
    have hi := @projectiveConfigurationFiniteSubschemeAtIsoConstantCover_component_toProjective
      _ _ _ _ _ (grading (equationIdeal p hp)) _ _ _
      (hypersurfaceToBase p hp) hsep' 8 A hBid i
    exact hi.trans (hcoords i)
  exact ⟨c, hc, q, A, B, D, hq, hqinj, hA, rfl, hBbase,
    ⟨hBid, rfl⟩, hDet, ⟨E, hSplit⟩, hcoords⟩

/-- The generic smooth cubic has an actual ordered eight-point
configuration whose marked vector representatives impose independent
quadratic conditions. -/
theorem exists_generic_ordered_eight_configuration_with_quadratic_witness
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ (y : Fin 8 → Fin 4 → L)
        (hzero : ∀ i, p.eval (y i) = 0),
        Function.Surjective
          (homogeneousSectionRestriction (K := L)
            (fun (j : Fin 4) (i : Fin 8) => y i j) 2) ∧
        (∀ i, (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y i) = 0 ∧
          (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y i) = 0) ∧
        (let x : Fin 4 → Fin 8 → L := fun j i => y i j
         let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
           ![(⟨(X 1 * X 2 : MvPolynomial (Fin 4) L),
             (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)⟩),
             (⟨(X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L),
               (isHomogeneous_X L 3).mul
                 (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
                   (isHomogeneous_X L 3))⟩)]
         (⟨(X 1 * X 2 : MvPolynomial (Fin 4) L),
           (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)⟩ :
             homogeneousSubmodule (Fin 4) L 2) ∈
               LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) ∧
         (⟨(X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L),
           (isHomogeneous_X L 3).mul
             (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
               (isHomogeneous_X L 3))⟩ :
             homogeneousSubmodule (Fin 4) L 2) ∈
               LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) ∧
         Module.finrank L (LinearMap.ker
           (homogeneousSectionRestriction (K := L) x 2)) = 2 ∧
         LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) =
           Submodule.span L (Set.range Q)) ∧
        ∃ (c : Fin 4 → L)
          (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0),
          ∃ (q : Fin 8 → (Spec (.of L) ⟶ hypersurface p hp))
            (A : Spec (.of L) ⟶
              (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
            (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
            (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8),
            (∀ i, q i = projectiveVectorSchemePointInLinearChart
              (equationIdeal p hp) c (y i)
              (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)) ∧
            Function.Injective q ∧
            A ≫ (orderedFamilyConfigurationOver
              (hypersurfaceToBase p hp) 8).hom =
                Spec.map (CommRingCat.ofHom (RingHom.id L)) ∧
            A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B ∧
            B ≫ cubicConfigurationToBase p hp 8 =
              Spec.map (CommRingCat.ofHom (RingHom.id L)) ∧
            (∃ hB : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _,
              D = projectiveConfigurationFiniteSubschemeAt
                (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8 B hB) ∧
            Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
            (∃ E : (∐ fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) ≅
                D.val.subscheme,
              ∀ i, Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
                (ULift.up i) ≫ E.hom ≫ D.val.subschemeι = q i) ∧
            (∀ i, (A ≫ Over.Hom.left
              (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
              (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left = q i) := by
  dsimp only
  letI : Infinite L := CharZero.infinite L
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨y, hsurj, hzero, hquadrics, hnonzero, hprojective⟩ :=
    generic_split_exists_finEight_projectively_distinct_quadratic_witness K φ
  let x : Fin 4 → Fin 8 → L := fun j i => y i j
  have hqker :
      (⟨(X 1 * X 2 : MvPolynomial (Fin 4) L),
        (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)⟩ :
        homogeneousSubmodule (Fin 4) L 2) ∈
          LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) := by
    apply LinearMap.mem_ker.mpr
    apply _root_.funext
    intro i
    simpa [x, homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply] using (hquadrics i).1
  have hrker :
      (⟨(X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L),
        (isHomogeneous_X L 3).mul
          (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
            (isHomogeneous_X L 3))⟩ :
        homogeneousSubmodule (Fin 4) L 2) ∈
          LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) := by
    apply LinearMap.mem_ker.mpr
    apply _root_.funext
    intro i
    simpa [x, homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply] using (hquadrics i).2
  have hkerdim : Module.finrank L (LinearMap.ker
      (homogeneousSectionRestriction (K := L) x 2)) = 2 :=
    quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
      x (by simp) hsurj
  have hspan := split_quadrics_span_eight_evaluation_kernel y hsurj hquadrics
  obtain ⟨c, hc, q, A, hq, hqinj, hA, hcoords⟩ :=
    exists_ordered_eight_configuration_of_cubic_vectors
      _ _ y hzero hnonzero hprojective
  let B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8 :=
    A ≫ configurationQuotientMap (equationIdeal p hp) 8
  have hBbase : B ≫ cubicConfigurationToBase p hp 8 =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    let I := equationIdeal p hp
    have hrel := configurationQuotientMap_toBase I 8
    calc
      B ≫ cubicConfigurationToBase p hp 8 =
          A ≫ (configurationQuotientMap I 8 ≫
            configurationQuotientToBase I 8) := by
              exact Category.assoc _ _ _
      _ = A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom :=
        congrArg (fun f => A ≫ f) hrel
      _ = _ := hA
  have hBid : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _ := by
    simpa using hBbase
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    @IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase p hp)
  have hsep' : IsSeparated (hypersurfaceToBase p hp) := inferInstance
  let D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8 :=
    projectiveConfigurationFiniteSubschemeAt
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8 B hBid
  have hDet : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) := by
    change Etale ((projectiveConfigurationFiniteSubschemeAt
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8 B hBid).val.subschemeι ≫
        hypersurfaceToBase p hp)
    exact @projectiveConfigurationFiniteSubschemeAt_toBase_etale
      _ _ _ _ _ (grading (equationIdeal p hp)) _ _ _
      (hypersurfaceToBase p hp) hsep' 8 B hBid
  let E : (∐ fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) ≅ D.val.subscheme :=
    @projectiveConfigurationFiniteSubschemeAtIsoConstantCover
      _ _ _ _ _ (grading (equationIdeal p hp)) _ _ _
      (hypersurfaceToBase p hp) hsep' 8 A hBid
  have hSplit : ∀ i,
      Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
        (ULift.up i) ≫ E.hom ≫ D.val.subschemeι = q i := by
    intro i
    have hi := @projectiveConfigurationFiniteSubschemeAtIsoConstantCover_component_toProjective
      _ _ _ _ _ (grading (equationIdeal p hp)) _ _ _
      (hypersurfaceToBase p hp) hsep' 8 A hBid i
    exact hi.trans (hcoords i)
  exact ⟨genericCubicTensor_smooth_baseChange K φ,
    y, hzero, hsurj, hquadrics, ⟨hqker, hrker, hkerdim, hspan⟩,
    c, hc, q, A, B, D, hq, hqinj, hA, rfl, hBbase,
    ⟨hBid, rfl⟩, hDet, ⟨E, hSplit⟩, hcoords⟩

/-- A rank-eight finite subscheme with eight labeled, distinct rational
points has the product algebra of its labels.  The labeled splitting is
retained in the hypotheses so the product coordinates can later be matched
to the actual projective vectors. -/
noncomputable def finiteEightDatum_coordinateAlgebra_equiv_pi_of_labeled_points_canonical
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (E : (∐ fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) ≅ D.val.subscheme)
    (q : Fin 8 → (Spec (.of L) ⟶ hypersurface p hp))
    (hpoint : ∀ i,
      Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
        (ULift.up i) ≫ E.hom ≫ D.val.subschemeι = q i)
    (hqbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (RingHom.id L)))
    (hqinj : Function.Injective q) :
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    Γ(D.val.subscheme, ⊤) ≃ₐ[L] (Fin 8 → L) := by
  let f := D.val.subschemeι ≫ hypersurfaceToBase p hp
  letI : IsFinite f := D.property.1
  letI := finiteSchemeCoefficientAlgebra f
  let x : Fin 8 → (Spec (.of L) ⟶ D.val.subscheme) :=
    fun i => Sigma.ι
      (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) (ULift.up i) ≫ E.hom
  have hxbase : ∀ i, x i ≫ f =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    intro i
    calc
      x i ≫ f = (x i ≫ D.val.subschemeι) ≫ hypersurfaceToBase p hp :=
        (Category.assoc _ _ _).symm
      _ = q i ≫ hypersurfaceToBase p hp :=
        congrArg (· ≫ hypersurfaceToBase p hp) (hpoint i)
      _ = _ := hqbase i
  have hxinj : Function.Injective x := by
    intro i j hij
    apply hqinj
    calc
      q i = x i ≫ D.val.subschemeι := (hpoint i).symm
      _ = x j ≫ D.val.subschemeι := congrArg (· ≫ D.val.subschemeι) hij
      _ = q j := hpoint j
  have hrank : finiteSchemeRank f = 8 :=
    finiteSubschemeDatum_finiteSchemeRank (hypersurfaceToBase p hp) D
  exact finiteSchemeCoefficient_equiv_pi_of_full_rational_points
    f x hxbase hxinj hrank

/-- Existence of the canonical labeled product-algebra splitting. -/
theorem finiteEightDatum_coordinateAlgebra_equiv_pi_of_labeled_points
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (E : (∐ fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) ≅ D.val.subscheme)
    (q : Fin 8 → (Spec (.of L) ⟶ hypersurface p hp))
    (hpoint : ∀ i,
      Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
        (ULift.up i) ≫ E.hom ≫ D.val.subschemeι = q i)
    (hqbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (RingHom.id L)))
    (hqinj : Function.Injective q) :
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    Nonempty (Γ(D.val.subscheme, ⊤) ≃ₐ[L] (Fin 8 → L)) :=
  ⟨finiteEightDatum_coordinateAlgebra_equiv_pi_of_labeled_points_canonical
    p hp D E q hpoint hqbase hqinj⟩

/-- Each component of the canonical splitting is evaluation at the
corresponding labeled section of the finite subscheme. -/
theorem finiteEightDatum_coordinateAlgebra_equiv_pi_canonical_apply
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (E : (∐ fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) ≅ D.val.subscheme)
    (q : Fin 8 → (Spec (.of L) ⟶ hypersurface p hp))
    (hpoint : ∀ i,
      Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
        (ULift.up i) ≫ E.hom ≫ D.val.subschemeι = q i)
    (hqbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (RingHom.id L)))
    (hqinj : Function.Injective q)
    (a : Γ(D.val.subscheme, ⊤)) (i : Fin 8) :
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI := finiteSchemeCoefficientAlgebra
      (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    let x : Fin 8 → (Spec (.of L) ⟶ D.val.subscheme) :=
      fun k => Sigma.ι
        (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) (ULift.up k) ≫ E.hom
    let hxbase : ∀ k, x k ≫
        (D.val.subschemeι ≫ hypersurfaceToBase p hp) =
        Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
      intro k
      dsimp only [x]
      simpa only [Category.assoc] using
        (congrArg (· ≫ hypersurfaceToBase p hp) (hpoint k)).trans
          (hqbase k)
    (finiteEightDatum_coordinateAlgebra_equiv_pi_of_labeled_points_canonical
      p hp D E q hpoint hqbase hqinj a) i =
      finiteSchemePointAlgHom
        (D.val.subschemeι ≫ hypersurfaceToBase p hp)
        (x i) (RingHom.id L) (hxbase i) a := by
  rfl

/-- The explicit generic smooth cubic has a genuine finite étale
eight-point configuration whose global algebra splits as eight copies
of the coefficient field, in the order of its marked projective points. -/
theorem exists_generic_eight_finite_datum_split_coordinate_algebra
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8,
        Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
        letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
        letI := finiteSchemeCoefficientAlgebra
          (D.val.subschemeι ≫ hypersurfaceToBase p hp)
        Nonempty (Γ(D.val.subscheme, ⊤) ≃ₐ[L] (Fin 8 → L)) := by
  dsimp only
  letI : Infinite L := CharZero.infinite L
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hsmooth, y, hzero, hsurj, hquadrics, hkernel,
    c, hc, q, A, B, D, hq, hqinj, hA, hAB, hB, hD,
    hEt, ⟨E, hE⟩, hcoords⟩ :=
    exists_generic_ordered_eight_configuration_with_quadratic_witness K φ
  have hqbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    intro i
    rw [hq i]
    exact projectiveVectorSchemePointInLinearChart_toBase
      (equationIdeal p hp) c (y i)
      (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)
  exact ⟨hsmooth, D, hEt,
    finiteEightDatum_coordinateAlgebra_equiv_pi_of_labeled_points
      p hp D E q hE hqbase hqinj⟩

end PfaffianDescent

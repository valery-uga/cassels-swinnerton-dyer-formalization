import PfaffianDescent.NegativeQuadricIdealFactorization
import PfaffianDescent.OriginalThreeQuadricAffineIdealGenerators
import PfaffianDescent.ClosedImmersionAffineGeneratorSurjectivity
import PfaffianDescent.ThreeQuadricSheafKoszulExactness

/-! SOURCE ONLY / UNVERIFIED. The actual last map onto the SAME original
length-eight immersion ideal is constructed internally. Its affine images
are the literal normalized three quadrics, its Epi proof is sheaf-local,
and middle exactness is reflected through the actual ideal inclusion. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
-- Actual production exposed Proj/module/sheaf aliases at the ring and zero morphisms.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K

-- Collapse a component before specializing the category to actual Proj modules.
private theorem originalQuadric_desc_comp_component
    {D : Type*} [Category D] [HasZeroMorphisms D] {ι : Type*}
    (P : ι → D) [HasBiproduct P] {Y W : D}
    (a : ∀ r, P r ⟶ Y) (m : Y ⟶ W) (r : ι) :
    biproduct.ι P r ≫ (biproduct.desc a ≫ m) = a r ≫ m := by
  rw [← Category.assoc, biproduct.ι_desc]

private theorem originalQuadric_last_component (f g h : PS 2) (r : Fin 3) :
    biproduct.ι (threeQuadricSheafTriple K 2) r ≫
      threeQuadricSheafKoszulLast K f g h =
        mulHomogeneousToUnit PS (![f, g, h] r) := by
  let b : ∀ r : Fin 3, threeQuadricSheafTriple K 2 r ⟶ sheafOfModules PS 0 :=
    ![threeQuadricSheafMul K f 0, threeQuadricSheafMul K g 0,
      threeQuadricSheafMul K h 0]
  have hc := originalQuadric_desc_comp_component
    (threeQuadricSheafTriple K 2) b (unitIsoZeroTwist PS).inv r
  have hm : b r ≫ (unitIsoZeroTwist PS).inv =
      mulHomogeneousToUnit PS (![f, g, h] r) := by
    fin_cases r <;> rfl
  exact hc.trans hm

private theorem originalQuadric_idealInclusion_mono
    {X Z : Scheme.{u}} (i : Z ⟶ X) :
    Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
  change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
  infer_instance

/-- The actual equations belong to the SAME original immersion kernels;
this is derived from the literal affine ideal, not assumed. -/
theorem p3OriginalThreeQuadric_equation_mem_intrinsic
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    (r : Fin 3) (j : Fin 4) :
    ((![f, g, h] r).val) ∈ intrinsicQuadraticChartIdeal (K := K) (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) j := by
  change (Proj.awayToSection PS (X j)).hom
    (ambientChartEvaluation j ((![f, g, h] r).val)) ∈
      (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)).ker.ideal (intrinsicQuadraticAmbientOpen (K := K) j)
  rw [p3OriginalThreeQuadric_affineIdeal_eq_span f g h l hZ j]
  exact Ideal.subset_span (Set.mem_range_self r)

/-- The actual three-generator map to the original ideal sheaf. -/
def p3OriginalThreeQuadricSheafAugmentation
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    (⨁ threeQuadricSheafTriple K 2) ⟶
      IdealSheafDataModule.closedImmersionModule (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) :=
  biproduct.desc (fun r : Fin 3 => p3NegativeQuadricToOriginalIdeal (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))
    (![f, g, h] r) (p3OriginalThreeQuadric_equation_mem_intrinsic f g h l hZ r))

@[reassoc]
theorem p3OriginalThreeQuadricSheafAugmentation_comp
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    p3OriginalThreeQuadricSheafAugmentation f g h l hZ ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) =
        threeQuadricSheafKoszulLast K f g h := by
  let i := l ≫ quotientProjMap (R := K) (σ := Fin 4)
    (tripleCompleteIntersectionHomogeneousIdeal (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)
  let a : ∀ r : Fin 3, threeQuadricSheafTriple K 2 r ⟶
      IdealSheafDataModule.closedImmersionModule i :=
    fun r => p3NegativeQuadricToOriginalIdeal i (![f, g, h] r)
      (p3OriginalThreeQuadric_equation_mem_intrinsic f g h l hZ r)
  apply biproduct.hom_ext'
  intro r
  have hc := originalQuadric_desc_comp_component (threeQuadricSheafTriple K 2)
    a (IdealSheafDataModule.closedImmersionModuleToUnit i) r
  have hm := p3NegativeQuadricToOriginalIdeal_comp i (![f, g, h] r)
    (p3OriginalThreeQuadric_equation_mem_intrinsic f g h l hZ r)
  exact (hc.trans hm).trans (originalQuadric_last_component f g h r).symm

private theorem p3OriginalThreeQuadricSheafAugmentation_affine_surjective
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    (j : Fin 4) (V : (Proj PS).affineOpens)
    (hV : V.1 ≤ p3StandardOpen (K := K) j) :
    Function.Surjective
      ((p3OriginalThreeQuadricSheafAugmentation f g h l hZ).val.app (op V.1)) := by
  let P := threeQuadricSheafTriple K 2
  let φ := p3OriginalThreeQuadricSheafAugmentation f g h l hZ
  obtain ⟨z, hz⟩ := p3NegativeQuadric_chartBasis_surjective K j V.1 hV
    (1 : Γ(Proj PS, V.1))
  let a : Fin 3 → Γ((⨁ P), V.1) :=
    fun r => (biproduct.ι P r).val.app (op V.1) z
  let c : Fin 3 → Γ(Proj PS, V.1) :=
    fun r => p3NegativeQuadricChartCoefficient K j V.1 hV (![f, g, h] r)
  have hgen : (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)).ker.ideal V = Ideal.span (Set.range c) := by
    rw [← (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)).ker.map_ideal (U := V) (V := intrinsicQuadraticAmbientOpen j) hV,
      p3OriginalThreeQuadric_affineIdeal_eq_span f g h l hZ j,
      Ideal.map_span, ← Set.range_comp']
    rfl
  have himage (r : Fin 3) :
      ((φ ≫ IdealSheafDataModule.closedImmersionModuleToUnit (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))).val.app (op V.1))
        (a r) = c r := by
    change ((p3OriginalThreeQuadricSheafAugmentation f g h l hZ ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))).val.app (op V.1))
      ((biproduct.ι P r).val.app (op V.1) z) = c r
    rw [p3OriginalThreeQuadricSheafAugmentation_comp]
    have he : biproduct.ι P r ≫ threeQuadricSheafKoszulLast K f g h =
        mulHomogeneousToUnit PS (![f, g, h] r) :=
      originalQuadric_last_component f g h r
    change ((biproduct.ι P r ≫ threeQuadricSheafKoszulLast K f g h).val.app
      (op V.1)) z = c r
    rw [he]
    have hcoeff := p3NegativeQuadric_mulToUnit_chartCoefficient K j V.1 hV
      (![f, g, h] r) z
    have hunit :
        ((negativeTwistTrivializationHom K j 2).val.app (op V.1) z :
          Γ(Proj PS, V.1)) = (1 : Γ(Proj PS, V.1)) := hz
    refine hcoeff.trans ?_
    exact (congrArg (fun t : Γ(Proj PS, V.1) =>
      @Mul.mul (Γ(Proj PS, V.1)) (inferInstance : Mul (Γ(Proj PS, V.1)))
        (c r) t) hunit).trans (mul_one (c r))
  exact closedImmersionModule_affineGeneratorMap_surjective (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) (⨁ P) φ V a c hgen himage

/-- Actual Epi onto I_originalZ, derived from normalized chart generators
and the surjective actual negative-twist basis on every affine subopen. -/
theorem p3OriginalThreeQuadricSheafAugmentation_epi
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    Epi (p3OriginalThreeQuadricSheafAugmentation f g h l hZ) := by
  apply schemeModule_epi_of_affineSubopens_cover_surjective
    (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)
    (p3StandardOpen (K := K)) (p3StandardOpen_iSup K)
  exact p3OriginalThreeQuadricSheafAugmentation_affine_surjective f g h l hZ

/-- The actual middle map lands in the kernel of the actual augmentation. -/
theorem p3OriginalThreeQuadricSheafKoszul_middle_augmentation_zero
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    threeQuadricSheafKoszulMiddle K f g h ≫
      p3OriginalThreeQuadricSheafAugmentation f g h l hZ = 0 := by
  let i := l ≫ quotientProjMap (R := K) (σ := Fin 4)
    (tripleCompleteIntersectionHomogeneousIdeal (K := K) (a := 2) (b := 2) (c := 2)
      f.val g.val h.val f.property g.property h.property)
  letI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) :=
    originalQuadric_idealInclusion_mono i
  rw [← cancel_mono (IdealSheafDataModule.closedImmersionModuleToUnit (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)))]
  rw [Category.assoc, p3OriginalThreeQuadricSheafAugmentation_comp]
  exact (threeQuadricSheafKoszul_middle_last_zero K f g h).trans
    zero_comp.symm

/-- The actual last two maps of the displayed resolution. -/
def p3OriginalThreeQuadricSheafKoszul_middleAugmentationShortComplex
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (threeQuadricSheafKoszulMiddle K f g h)
    (p3OriginalThreeQuadricSheafAugmentation f g h l hZ)
    (p3OriginalThreeQuadricSheafKoszul_middle_augmentation_zero f g h l hZ)

/-- Genuine exactness at O(-2)^3 for the SAME original scheme. -/
theorem p3OriginalThreeQuadricSheafKoszul_middleAugmentation_exact
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    (p3OriginalThreeQuadricSheafKoszul_middleAugmentationShortComplex f g h l hZ).Exact := by
  let S := p3OriginalThreeQuadricSheafKoszul_middleAugmentationShortComplex f g h l hZ
  let R := threeQuadricSheafKoszul_middleLastShortComplex K f g h
  let φ : S ⟶ R := ShortComplex.homMk (𝟙 _) (𝟙 _)
    (IdealSheafDataModule.closedImmersionModuleToUnit (l ≫ quotientProjMap (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)))
    (by simp [S, R, p3OriginalThreeQuadricSheafKoszul_middleAugmentationShortComplex,
      threeQuadricSheafKoszul_middleLastShortComplex])
    (by
      change 𝟙 _ ≫ threeQuadricSheafKoszulLast K f g h =
        p3OriginalThreeQuadricSheafAugmentation f g h l hZ ≫ _
      exact (Category.id_comp (threeQuadricSheafKoszulLast K f g h)).trans
        (p3OriginalThreeQuadricSheafAugmentation_comp f g h l hZ).symm)
  letI : Epi φ.τ₁ := by
    change Epi (𝟙 S.X₁)
    infer_instance
  letI : IsIso φ.τ₂ := by
    change IsIso (𝟙 S.X₂)
    infer_instance
  letI : Mono φ.τ₃ := by
    change Mono (IdealSheafDataModule.closedImmersionModuleToUnit
      (l ≫ quotientProjMap (R := K) (σ := Fin 4)
        (tripleCompleteIntersectionHomogeneousIdeal (K := K) (a := 2) (b := 2) (c := 2)
          f.val g.val h.val f.property g.property h.property)))
    exact originalQuadric_idealInclusion_mono _
  have hT := p3ThreeQuadricOriginalLift_nonempty f g h l hZ
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
  exact threeQuadricSheafKoszul_middleLast_exact K f g h hT

/-- All exactness assertions of the untwisted displayed ideal resolution,
with the actual left map and actual original ideal target. -/
theorem p3OriginalThreeQuadricSheafKoszul_displayed_resolution
    (f g h : PS 2)
    [IsFinite (toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank
      (l ≫ toBase (R := K) (σ := Fin 4) (tripleCompleteIntersectionHomogeneousIdeal
        (K := K) (a := 2) (b := 2) (c := 2)
        f.val g.val h.val f.property g.property h.property)) = 8)
    :
    Mono (threeQuadricSheafKoszulFirst K f g h) ∧
    (threeQuadricSheafKoszul_firstMiddleShortComplex K f g h).Exact ∧
    (p3OriginalThreeQuadricSheafKoszul_middleAugmentationShortComplex f g h l hZ).Exact ∧
    Epi (p3OriginalThreeQuadricSheafAugmentation f g h l hZ) := by
  have hT := p3ThreeQuadricOriginalLift_nonempty f g h l hZ
  have hseq := AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    f.val g.val h.val f.property g.property h.property hT
  obtain ⟨hf0, _, _⟩ :=
    (triple_quadrics_isRegular_iff_sequential_regular
      f.val g.val h.val f.property g.property h.property).mp hseq
  exact ⟨threeQuadricSheafKoszulFirst_mono K f g h hf0,
    threeQuadricSheafKoszul_firstMiddle_exact K f g h hT,
    p3OriginalThreeQuadricSheafKoszul_middleAugmentation_exact f g h l hZ,
    p3OriginalThreeQuadricSheafAugmentation_epi f g h l hZ⟩

end PfaffianDescent.ProjectiveNegativeTwist

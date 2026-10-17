import PfaffianDescent.CorayActualDegreeZeroChartPresentation
import PfaffianDescent.VoisinPositiveTwistTriviality
import PfaffianDescent.SchemeModuleBaseLinearCategory
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-! Actual finite coproducts of positive twists, with the SAME homogeneous
polynomial generator and relation matrices. No global section lifting or
Serre conclusion is a premise. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open ProjectiveNegativeTwist
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The actual positive multiplication map, with only the required equality
of complementary natural degrees inserted at its target. -/
def actualPositiveWeightedMultiplication (p : A) {d : ℕ}
    (hp : p.IsHomogeneous d) (a b : ℕ) (h : a + d = b) :
    positiveSheafOfModules PS a ⟶ positiveSheafOfModules PS b :=
  positiveMulHomogeneous PS ⟨p, hp⟩ a ≫
    eqToHom (congrArg (positiveSheafOfModules PS) h)

/-- The degree equality does not alter the actual fraction representing the
section. Thus the map still multiplies by the original polynomial. -/
theorem actualPositiveWeightedMultiplication_apply_val (p : A) {d : ℕ}
    (hp : p.IsHomogeneous d) (a b : ℕ) (h : a + d = b)
    (U : (Proj PS).Opens)
    (z : (positiveSheafOfModules PS a).val.obj (op U)) (x : U) :
    ((actualPositiveWeightedMultiplication p hp a b h).val.app (op U) z).1 x =
      algebraMap A (PositiveFiber PS x.1) p * z.1 x := by
  cases h
  rfl

/-- Actual finite positive generators at degree m. Every summand is the
OWN O(m-d_i), and each inclusion is the native categorical coproduct map. -/
def actualPositiveFiniteGeneratorMap {ι : Type u} [Fintype ι]
    (g : ι → A) (d : ι → ℕ) (hg : ∀ i, (g i).IsHomogeneous (d i))
    (m : ℕ) (hm : ∀ i, d i ≤ m) :
    (∐ fun i => positiveSheafOfModules PS (m - d i)) ⟶
      positiveSheafOfModules PS m :=
  Sigma.desc (fun i => actualPositiveWeightedMultiplication
    (g i) (hg i) (m - d i) m (by have := hm i; omega))

/-- One literal weighted relation entry, including the forced zero entries
when the source relation weight is below a generator weight. -/
def actualPositiveFiniteRelationEntry {ι : Type u}
    (d : ι → ℕ) (r : ι → A) (e : ℕ)
    (hr : ActualWeightedPolynomialHomogeneous d e r)
    (m : ℕ) (hm : e ≤ m) (i : ι) :
    positiveSheafOfModules PS (m - e) ⟶
      positiveSheafOfModules PS (m - d i) := by
  classical
  exact if hi : d i ≤ e then
    actualPositiveWeightedMultiplication (r i) (hr i).1
      (m - e) (m - d i) (by omega)
  else 0

/-- The actual relation column into the finite coproduct of generators. -/
def actualPositiveFiniteRelationColumn {ι : Type u} [Fintype ι]
    (d : ι → ℕ) (r : ι → A) (e : ℕ)
    (hr : ActualWeightedPolynomialHomogeneous d e r)
    (m : ℕ) (hm : e ≤ m) :
    positiveSheafOfModules PS (m - e) ⟶
      (∐ fun i => positiveSheafOfModules PS (m - d i)) :=
  ∑ i, actualPositiveFiniteRelationEntry d r e hr m hm i ≫
    Sigma.ι (fun i => positiveSheafOfModules PS (m - d i)) i

/-- The literal relation matrix assembled as an actual positive sheaf map. -/
def actualPositiveFiniteRelationMap {ι κ : Type u} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (m : ℕ) (hm : ∀ a, e a ≤ m) :
    (∐ fun a => positiveSheafOfModules PS (m - e a)) ⟶
      (∐ fun i => positiveSheafOfModules PS (m - d i)) :=
  Sigma.desc (fun a => actualPositiveFiniteRelationColumn
    d (r a) (e a) (hr a) m (hm a))

/-- Evaluate a native sheaf Hom at an actual section and an actual point.
This additive map handles finite Hom sums without unfolding a coproduct. -/
private def positiveHomSectionValue {M : (Proj PS).Modules} (m : ℕ)
    (U : (Proj PS).Opens) (z : M.val.obj (op U)) (x : U) :
    (M ⟶ positiveSheafOfModules PS m) →+ PositiveFiber PS x.1 where
  toFun f := (f.val.app (op U) z).1 x
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem actualPositiveFiniteRelationEntry_generator_val
    {ι : Type u} [Fintype ι] (g : ι → A) (d : ι → ℕ)
    (hg : ∀ i, (g i).IsHomogeneous (d i))
    (r : ι → A) (e : ℕ) (hr : ActualWeightedPolynomialHomogeneous d e r)
    (m : ℕ) (hd : ∀ i, d i ≤ m) (he : e ≤ m) (i : ι)
    (U : (Proj PS).Opens)
    (z : (positiveSheafOfModules PS (m - e)).val.obj (op U)) (x : U) :
    positiveHomSectionValue m U z x
      (actualPositiveFiniteRelationEntry d r e hr m he i ≫
        actualPositiveWeightedMultiplication (g i) (hg i)
          (m - d i) m (by have := hd i; omega)) =
      (algebraMap A (PositiveFiber PS x.1) (g i) *
        algebraMap A (PositiveFiber PS x.1) (r i)) * z.1 x := by
  classical
  by_cases hi : d i ≤ e
  · simp only [actualPositiveFiniteRelationEntry, dif_pos hi]
    change ((actualPositiveWeightedMultiplication (g i) (hg i)
      (m - d i) m (by have := hd i; omega)).val.app (op U)
      ((actualPositiveWeightedMultiplication (r i) (hr i).1
        (m - e) (m - d i) (by omega)).val.app (op U) z)).1 x = _
    rw [actualPositiveWeightedMultiplication_apply_val,
      actualPositiveWeightedMultiplication_apply_val, mul_assoc]
  · have hz : r i = 0 := (hr i).2 (Nat.lt_of_not_ge hi)
    simp only [actualPositiveFiniteRelationEntry, dif_neg hi,
      zero_comp, map_zero, hz, mul_zero, zero_mul]

/-- A genuine polynomial relation produces a zero composite of the actual
positive sheaf maps, not an assumed sheaf exactness certificate. -/
theorem actualPositiveFiniteRelationColumn_comp_generator_eq_zero
    {ι : Type u} [Fintype ι] (g : ι → A) (d : ι → ℕ)
    (hg : ∀ i, (g i).IsHomogeneous (d i))
    (r : ι → A) (e : ℕ) (hr : ActualWeightedPolynomialHomogeneous d e r)
    (hker : actualPolynomialGeneratorMap g r = 0)
    (m : ℕ) (hd : ∀ i, d i ≤ m) (he : e ≤ m) :
    actualPositiveFiniteRelationColumn d r e hr m he ≫
      actualPositiveFiniteGeneratorMap g d hg m hd = 0 := by
  classical
  unfold actualPositiveFiniteRelationColumn actualPositiveFiniteGeneratorMap
  rw [Preadditive.sum_comp]
  simp only [Category.assoc, Sigma.ι_desc]
  apply schemeModuleHom_ext_sections
  intro U z
  apply Subtype.ext
  funext x
  change U at x
  change positiveHomSectionValue m U z x
    (∑ i, actualPositiveFiniteRelationEntry d r e hr m he i ≫
      actualPositiveWeightedMultiplication (g i) (hg i) (m - d i) m _) = 0
  rw [map_sum]
  have hentry :
      (∑ i, positiveHomSectionValue m U z x
        (actualPositiveFiniteRelationEntry d r e hr m he i ≫
          actualPositiveWeightedMultiplication (g i) (hg i)
            (m - d i) m (by have := hd i; omega))) =
      (∑ i, algebraMap A (PositiveFiber PS x.1) (g i) *
        algebraMap A (PositiveFiber PS x.1) (r i)) * z.1 x := by
    calc
      _ = ∑ i, (algebraMap A (PositiveFiber PS x.1) (g i) *
          algebraMap A (PositiveFiber PS x.1) (r i)) * z.1 x := by
        apply Finset.sum_congr rfl
        intro i hi
        exact actualPositiveFiniteRelationEntry_generator_val
          g d hg r e hr m hd he i U z x
      _ = _ := (Finset.sum_mul Finset.univ _ (z.1 x)).symm
  have hc : (∑ i, algebraMap A (PositiveFiber PS x.1) (g i) *
      algebraMap A (PositiveFiber PS x.1) (r i)) = 0 := by
    have hpoly : (∑ i, g i * r i) = 0 := hker
    have h := congrArg (algebraMap A (PositiveFiber PS x.1)) hpoly
    simpa only [map_sum, map_mul, map_zero] using h
  exact hentry.trans (by rw [hc, zero_mul])

/-- The actual finite relation matrix and generator map form a native
short complex of sheaves on the original ambient projective space. -/
def actualPositiveFinitePresentationComplex
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (d : ι → ℕ) (hg : ∀ i, (g i).IsHomogeneous (d i))
    (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (hker : ∀ a, actualPolynomialGeneratorMap g (r a) = 0)
    (m : ℕ) (hd : ∀ i, d i ≤ m) (he : ∀ a, e a ≤ m) :
    ShortComplex (Proj PS).Modules :=
  ShortComplex.mk (actualPositiveFiniteRelationMap d r e hr m he)
    (actualPositiveFiniteGeneratorMap g d hg m hd) (by
      apply Sigma.hom_ext
      intro a
      simp only [actualPositiveFiniteRelationMap, Sigma.ι_desc_assoc, comp_zero]
      exact actualPositiveFiniteRelationColumn_comp_generator_eq_zero
        g d hg (r a) (e a) (hr a) (hker a) m hd (he a))

/-- Every actual homogeneous ideal supplies the SAME finite generators and
OWN kernel relations for the global positive complex and every normalized
native chart. No exactness or image certificate is supplied to this caller. -/
theorem homogeneousIdeal_exists_actualPositiveFiniteCoproductPresentationData
    (I : HomogeneousIdeal PS) :
    ∃ (T : Finset A) (d : T → ℕ) (R : Finset (T → A)) (e : R → ℕ) (B : ℕ),
      Ideal.span (T : Set A) = I.toIdeal ∧
      (∀ i : T, d i ≤ B ∧ (i : A).IsHomogeneous (d i)) ∧
      Submodule.span A (R : Set (T → A)) =
        (actualPolynomialGeneratorMap (fun i : T => i.val)).ker ∧
      (∀ a : R, e a ≤ B ∧ ActualWeightedPolynomialHomogeneous d (e a) a.val) ∧
      (∀ a : R, actualPolynomialGeneratorMap (fun i : T => i.val) a.val = 0) ∧
      ∀ j : Fin 4,
        Function.Exact (actualDegreeZeroChartRelationMap j (fun a : R => a.val))
          (actualDegreeZeroChartGeneratorMap j (fun i : T => i.val)) ∧
        (actualDegreeZeroChartGeneratorMap j (fun i : T => i.val)).range =
          RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j) := by
  classical
  obtain ⟨T, d, R, e, B, hT, hd, hR, he⟩ :=
    homogeneousIdeal_exists_actual_finite_homogeneousPresentation_and_relations I
  have hker : ∀ a : R,
      actualPolynomialGeneratorMap (fun i : T => i.val) a.val = 0 := by
    intro a
    apply LinearMap.mem_ker.mp
    rw [← hR]
    exact Submodule.subset_span a.property
  have hTset : Set.range (fun i : T => i.val) = (T : Set A) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩; exact i.property
    · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
  have hRset : Set.range (fun a : R => a.val) = (R : Set (T → A)) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩; exact i.property
    · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
  have hg : Ideal.span (Set.range (fun i : T => i.val)) = I.toIdeal := by
    rw [hTset]; exact hT
  have hr : Submodule.span A (Set.range (fun a : R => a.val)) =
      (actualPolynomialGeneratorMap (fun i : T => i.val)).ker := by
    rw [hRset]; exact hR
  refine ⟨T, d, R, e, B, hT, hd, hR, he, hker, fun j => ?_⟩
  exact ⟨actualDegreeZeroChartPresentation_exact I (fun i : T => i.val)
      (fun a : R => a.val) hg hr j,
    actualDegreeZeroChartGeneratorMap_range_eq_quotientKernel I (fun i : T => i.val) hg j⟩

end PfaffianDescent.Coray

import PfaffianDescent.CorayActualHomogeneousIdealPresentation
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-! Weighted homogeneous generators for the SAME actual relation kernel.
No homogeneous relation or finite presentation certificate is supplied to
its actual kernel caller. SOURCE ONLY UNVERIFIED; root owns all checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u v
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual weighted degree projection in a polynomial free module.
A coefficient whose generator weight exceeds the degree is zero. -/
def actualWeightedPolynomialComponent
    {ι : Type v} (d : ι → ℕ) (m : ℕ)
    (c : ι → MvPolynomial (Fin 4) K) : ι → MvPolynomial (Fin 4) K :=
  fun i => if d i ≤ m then homogeneousComponent (m - d i) (c i) else 0

/-- The literal weighted homogeneous condition, including coefficients
which necessarily vanish below their generator weights. -/
def ActualWeightedPolynomialHomogeneous
    {ι : Type v} (d : ι → ℕ) (m : ℕ)
    (c : ι → MvPolynomial (Fin 4) K) : Prop :=
  ∀ i, (c i).IsHomogeneous (m - d i) ∧ (m < d i → c i = 0)

/-- Every actual weighted degree projection is homogeneous at that weight. -/
theorem actualWeightedPolynomialComponent_isHomogeneous
    {ι : Type v} (d : ι → ℕ) (m : ℕ)
    (c : ι → MvPolynomial (Fin 4) K) :
    ActualWeightedPolynomialHomogeneous d m
      (actualWeightedPolynomialComponent d m c) := by
  intro i
  by_cases hi : d i ≤ m
  · simp only [actualWeightedPolynomialComponent, if_pos hi]
    exact ⟨homogeneousComponent_isHomogeneous _ _, fun h => (Nat.not_lt.mpr hi h).elim⟩
  · simp only [actualWeightedPolynomialComponent, if_neg hi]
    exact ⟨MvPolynomial.isHomogeneous_zero (Fin 4) K (m - d i), fun _ => True.intro⟩

private theorem actualPolynomial_sum_homogeneousComponent_of_bound
    (a : MvPolynomial (Fin 4) K) (B : ℕ) (hB : a.totalDegree ≤ B) :
    (∑ m ∈ Finset.range (B + 1), homogeneousComponent m a) = a := by
  calc
    (∑ m ∈ Finset.range (B + 1), homogeneousComponent m a) =
        ∑ m ∈ Finset.range (a.totalDegree + 1), homogeneousComponent m a := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro m hm hnot
      apply homogeneousComponent_eq_zero
      have hnot' : ¬m < a.totalDegree + 1 := by
        simpa only [Finset.mem_range] using hnot
      omega
    _ = a := sum_homogeneousComponent a

/-- Every actual polynomial coefficient vector is the finite sum of its
actual weighted homogeneous components. The bound is constructed from its
own polynomial total degrees and the supplied natural generator weights. -/
theorem actualWeightedPolynomialComponent_reconstruction
    {ι : Type v} [Fintype ι] (d : ι → ℕ)
    (c : ι → MvPolynomial (Fin 4) K) :
    ∃ B : ℕ, (∑ m ∈ Finset.range (B + 1),
      actualWeightedPolynomialComponent d m c) = c := by
  classical
  let B := Finset.univ.sup (fun i : ι => d i + (c i).totalDegree)
  refine ⟨B, ?_⟩
  funext i
  rw [Finset.sum_apply]
  change (∑ m ∈ Finset.range (B + 1),
    if d i ≤ m then homogeneousComponent (m - d i) (c i) else 0) = c i
  have hbound : d i + (c i).totalDegree ≤ B :=
    Finset.le_sup (f := fun j : ι => d j + (c j).totalDegree)
      (Finset.mem_univ i)
  have hindex : B + 1 = d i + (B - d i + 1) := by omega
  rw [hindex, Finset.sum_range_add]
  have hfirst : (∑ m ∈ Finset.range (d i),
      if d i ≤ m then homogeneousComponent (m - d i) (c i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg (Nat.not_le.mpr (Finset.mem_range.mp hm))]
  rw [hfirst, zero_add]
  calc
    (∑ m ∈ Finset.range (B - d i + 1),
        if d i ≤ d i + m then homogeneousComponent (d i + m - d i) (c i) else 0) =
        ∑ m ∈ Finset.range (B - d i + 1), homogeneousComponent m (c i) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [if_pos (by omega), Nat.add_sub_cancel_left]
    _ = c i := actualPolynomial_sum_homogeneousComponent_of_bound
      (c i) (B - d i) (by omega)

/-- The SAME literal generator map commutes with weighted degree projection
at every degree, including degrees below some generator weights. -/
theorem actualPolynomialGeneratorMap_weightedComponent
    {ι : Type v} [Fintype ι] (g : ι → MvPolynomial (Fin 4) K)
    (d : ι → ℕ) (hhom : ∀ i, (g i).IsHomogeneous (d i))
    (m : ℕ) (c : ι → MvPolynomial (Fin 4) K) :
    actualPolynomialGeneratorMap g (actualWeightedPolynomialComponent d m c) =
      homogeneousComponent m (actualPolynomialGeneratorMap g c) := by
  change (∑ i, g i * actualWeightedPolynomialComponent d m c i) =
    homogeneousComponent m (∑ i, g i * c i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hdi : d i ≤ m
  · simp only [actualWeightedPolynomialComponent, if_pos hdi]
    have hindex : d i + (m - d i) = m := by omega
    have hmul := PfaffianDescent.homogeneousComponent_mul_left
      (q := c i) (hhom i) (m - d i)
    rw [hindex] at hmul
    exact hmul.symm
  · simp only [actualWeightedPolynomialComponent, if_neg hdi, mul_zero]
    have hzero := PfaffianDescent.homogeneousComponent_mul_right_of_lt
      (p := c i) (hhom i) (Nat.lt_of_not_ge hdi)
    simpa only [mul_comm] using hzero.symm

/-- A literal weighted-homogeneous polynomial submodule has internally
constructed finite homogeneous generators and a derived common degree
bound. Its homogeneity is a natural generic hypothesis; the actual relation
kernel caller below proves it from the SAME actual generator map. -/
theorem actualWeightedPolynomialSubmodule_exists_bounded_homogeneousGenerators
    {ι : Type v} [Fintype ι] (d : ι → ℕ)
    (N : Submodule (MvPolynomial (Fin 4) K) (ι → MvPolynomial (Fin 4) K))
    (hN : ∀ m c, c ∈ N → actualWeightedPolynomialComponent d m c ∈ N) :
    ∃ (T : Finset (ι → MvPolynomial (Fin 4) K)) (e : T → ℕ) (B : ℕ),
      Submodule.span (MvPolynomial (Fin 4) K)
        (T : Set (ι → MvPolynomial (Fin 4) K)) = N ∧
      ∀ c : T, e c ≤ B ∧ ActualWeightedPolynomialHomogeneous d (e c) c.val := by
  classical
  let S : Set (ι → MvPolynomial (Fin 4) K) :=
    {c | c ∈ N ∧ ∃ m : ℕ, ActualWeightedPolynomialHomogeneous d m c}
  have hspan : Submodule.span (MvPolynomial (Fin 4) K) S = N := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (fun c hc => hc.1)
    · intro c hc
      obtain ⟨B, hB⟩ := actualWeightedPolynomialComponent_reconstruction d c
      rw [← hB]
      apply Submodule.sum_mem
      intro m hm
      apply Submodule.subset_span
      exact ⟨hN m c hc, m, actualWeightedPolynomialComponent_isHomogeneous d m c⟩
  have hfg : (Submodule.span (MvPolynomial (Fin 4) K) S).FG := by
    rw [hspan]
    exact IsNoetherian.noetherian N
  obtain ⟨T, hT, hTspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset S).mp hfg
  have hhom : ∀ c : T, ∃ m : ℕ, ActualWeightedPolynomialHomogeneous d m c.val :=
    fun c => (hT c.property).2
  choose e he using hhom
  refine ⟨T, e, Finset.univ.sup e, hTspan.symm.trans hspan, ?_⟩
  intro c
  exact ⟨Finset.le_sup (Finset.mem_univ c), he c⟩

/-- Actual finite homogeneous syzygies of the OWN literal ideal presentation.
No finite relation data or desired syzygy certificate is a caller premise;
polynomial Noetherianity and the actual generator map construct them. -/
theorem actualPolynomialGeneratorMap_kernel_exists_bounded_homogeneousGenerators
    {ι : Type v} [Fintype ι] (g : ι → MvPolynomial (Fin 4) K)
    (d : ι → ℕ) (hhom : ∀ i, (g i).IsHomogeneous (d i)) :
    ∃ (T : Finset (ι → MvPolynomial (Fin 4) K)) (e : T → ℕ) (B : ℕ),
      Submodule.span (MvPolynomial (Fin 4) K)
        (T : Set (ι → MvPolynomial (Fin 4) K)) = (actualPolynomialGeneratorMap g).ker ∧
      ∀ c : T, e c ≤ B ∧ ActualWeightedPolynomialHomogeneous d (e c) c.val := by
  apply actualWeightedPolynomialSubmodule_exists_bounded_homogeneousGenerators d
    (actualPolynomialGeneratorMap g).ker
  intro m c hc
  apply LinearMap.mem_ker.mpr
  rw [actualPolynomialGeneratorMap_weightedComponent g d hhom m c,
    LinearMap.mem_ker.mp hc, map_zero]

/-- A primitive OWN homogeneous ideal has finite homogeneous generators
and finite homogeneous syzygies of their SAME literal polynomial map.
All data and both degree bounds are internally derived. -/
theorem homogeneousIdeal_exists_actual_finite_homogeneousPresentation_and_relations
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    ∃ (T : Finset (MvPolynomial (Fin 4) K)) (d : T → ℕ)
      (R : Finset (T → MvPolynomial (Fin 4) K)) (e : R → ℕ) (B : ℕ),
      Ideal.span (T : Set (MvPolynomial (Fin 4) K)) = I.toIdeal ∧
      (∀ i : T, d i ≤ B ∧ (i : MvPolynomial (Fin 4) K).IsHomogeneous (d i)) ∧
      Submodule.span (MvPolynomial (Fin 4) K)
        (R : Set (T → MvPolynomial (Fin 4) K)) =
          (actualPolynomialGeneratorMap (fun i : T => i.val)).ker ∧
      ∀ c : R, e c ≤ B ∧ ActualWeightedPolynomialHomogeneous d (e c) c.val := by
  classical
  obtain ⟨T, A, hspan, hgen⟩ :=
    homogeneousIdeal_exists_finite_homogeneousGenerators_with_degreeBound I
  have hgen' : ∀ i : T, ∃ d : ℕ,
      d ≤ A ∧ (i : MvPolynomial (Fin 4) K).IsHomogeneous d :=
    fun i => hgen i.val i.property
  choose d hd using hgen'
  obtain ⟨R, e, B, hrel, hR⟩ :=
    actualPolynomialGeneratorMap_kernel_exists_bounded_homogeneousGenerators
      (fun i : T => i.val) d (fun i => (hd i).2)
  refine ⟨T, d, R, e, max A B, hspan, ?_, hrel, ?_⟩
  · intro i
    exact ⟨(hd i).1.trans (le_max_left A B), (hd i).2⟩
  · intro c
    exact ⟨(hR c).1.trans (le_max_right A B), (hR c).2⟩

end PfaffianDescent.Coray

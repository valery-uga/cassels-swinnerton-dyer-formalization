import PfaffianDescent.CorayActualPresentationNativeLocalizationSheafExact
import PfaffianDescent.IntrinsicFullQuadraticSystem

/-! The OWN homogeneous presentation in the actual degree-zero Proj chart.
Normalized evaluation and the actual quotient chart map are kept literally.
SOURCE ONLY UNVERIFIED; root owns compiler and acceptance. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Setting a coordinate equal to one creates no extra annihilator in the
OWN homogeneous quotient. This is proved from its actual homogeneous
components, even if that quotient has nilpotents or zero divisors. -/
theorem homogeneousIdeal_coordinate_sub_one_saturated
    (I : HomogeneousIdeal PS) (j : Fin 4) (a : A)
    (ha : (X j - 1) * a ∈ I.toIdeal) : a ∈ I.toIdeal := by
  apply (MvPolynomial.mem_iff_homogeneousComponent_mem I.isHomogeneous a).mpr
  intro n
  induction n with
  | zero =>
      have h := MvPolynomial.homogeneousComponent_mem_of_mem I.isHomogeneous ha 0
      have hz : homogeneousComponent 0 (X j * a) = 0 := by
        simpa only [mul_comm] using
          PfaffianDescent.homogeneousComponent_mul_right_of_lt
            (p := a) (isHomogeneous_X K j) (by decide : 0 < 1)
      have hneg : -homogeneousComponent 0 a ∈ I.toIdeal := by
        simpa only [sub_mul, one_mul, map_sub, hz, zero_sub] using h
      exact (I.toIdeal.neg_mem_iff).mp hneg
  | succ n ih =>
      have h := MvPolynomial.homogeneousComponent_mem_of_mem I.isHomogeneous ha (n + 1)
      have hmul : homogeneousComponent (n + 1) (X j * a) =
          X j * homogeneousComponent n a := by
        simpa only [Nat.add_comm] using
          PfaffianDescent.homogeneousComponent_mul_left (q := a)
            (isHomogeneous_X K j) n
      have hdiff : X j * homogeneousComponent n a -
          homogeneousComponent (n + 1) a ∈ I.toIdeal := by
        simpa only [sub_mul, one_mul, map_sub, hmul] using h
      have hsub := I.toIdeal.sub_mem (I.toIdeal.mul_mem_left (X j) ih) hdiff
      convert hsub using 1 <;> ring

/-- The finite generator matrix on the actual degree-zero coordinate chart.
Its scalar action is the chart ring's OWN standard module action. -/
def actualDegreeZeroChartGeneratorMap
    {ι : Type u} [Fintype ι] (j : Fin 4) (g : ι → A) :
    (ι → HomogeneousLocalization.Away PS (X j)) →ₗ[HomogeneousLocalization.Away PS (X j)]
      HomogeneousLocalization.Away PS (X j) where
  toFun c := ∑ i, ambientChartEvaluation j (g i) * c i
  map_add' c c' := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_left_comm _ a (c i)

/-- The relation columns are normalized by the SAME actual chart
homomorphism, rather than replaced by an unrelated local kernel. -/
def actualDegreeZeroChartRelationMap
    {ι κ : Type u} [Fintype ι] [Fintype κ] (j : Fin 4) (r : κ → ι → A) :
    (κ → HomogeneousLocalization.Away PS (X j)) →ₗ[HomogeneousLocalization.Away PS (X j)]
      (ι → HomogeneousLocalization.Away PS (X j)) where
  toFun c := ∑ a, c a • (fun i => ambientChartEvaluation j (r a i))
  map_add' c c' := by
    funext i
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_assoc]

/-- The actual polynomial generator map specializes to the literal
normalized chart generator matrix. -/
theorem actualDegreeZeroChartGeneratorMap_evaluate
    {ι : Type u} [Fintype ι] (j : Fin 4) (g c : ι → A) :
    actualDegreeZeroChartGeneratorMap j g (fun i => ambientChartEvaluation j (c i)) =
      ambientChartEvaluation j (actualPolynomialGeneratorMap g c) := by
  change (∑ i, ambientChartEvaluation j (g i) * ambientChartEvaluation j (c i)) =
    ambientChartEvaluation j (∑ i, g i * c i)
  simp only [map_sum, map_mul]

/-- The actual polynomial relation matrix specializes to the literal
normalized chart relation matrix, component by component. -/
theorem actualDegreeZeroChartRelationMap_evaluate
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (j : Fin 4) (r : κ → ι → A) (c : κ → A) :
    actualDegreeZeroChartRelationMap j r (fun a => ambientChartEvaluation j (c a)) =
      fun i => ambientChartEvaluation j (actualPolynomialRelationMap r c i) := by
  funext i
  change (∑ a, ambientChartEvaluation j (c a) •
      (fun i => ambientChartEvaluation j (r a i))) i =
    ambientChartEvaluation j ((∑ a, c a • r a) i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]

/- Genuine algebraic correction before evaluating in the chart. This cut
contains ONLY the original polynomial module and original whole homogeneous
ideal; no projective localization carrier is unfolded here. -/
private theorem actualPolynomialPresentation_coordinate_correction
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (j : Fin 4) (c : ι → A)
    (hmem : actualPolynomialGeneratorMap g c ∈
      Ideal.span ({(X j : A) - 1} : Set A)) :
    ∃ (b : ι → A) (t : κ → A),
      actualPolynomialRelationMap r t = c - ((X j : A) - 1) • b := by
  classical
  let G : (ι → A) →ₗ[A] A := actualPolynomialGeneratorMap g
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hmem
  have hGa : ((X j : A) - 1) * a = G c := ha.symm
  have hGc : G c ∈ I.toIdeal := by
    rw [← hg]
    change (∑ i, g i * c i) ∈ Ideal.span (Set.range g)
    apply Ideal.sum_mem
    intro i hi
    exact Ideal.mul_mem_right (c i) _ (Ideal.subset_span ⟨i, rfl⟩)
  have haI : a ∈ I.toIdeal := homogeneousIdeal_coordinate_sub_one_saturated I j a
    (hGa.symm ▸ hGc)
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hg.symm ▸ haI)
  have hGb : G b = a := by
    change (∑ i, g i * b i) = a
    simpa only [mul_comm] using hb
  let c' : ι → A := c - ((X j : A) - 1) • b
  have hker : c' ∈ G.ker := by
    apply LinearMap.mem_ker.mpr
    change G (c - ((X j : A) - 1) • b) = 0
    rw [map_sub, map_smul, hGb, smul_eq_mul, hGa, sub_self]
  have hspan : c' ∈ Submodule.span A (Set.range r) := hr.symm ▸ hker
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hspan
  exact ⟨b, t, ht⟩

/- This is the ACTUAL distinguished-coordinate relation, derived from the
native normalized evaluation kernel. -/
private theorem actualAmbientChartEvaluation_coordinate_sub_one (j : Fin 4) :
    ambientChartEvaluation (R := K) (σ := Fin 4) j ((X j : A) - 1) = 0 := by
  change (X j : A) - 1 ∈ RingHom.ker
    (ambientChartEvaluation (R := K) (σ := Fin 4) j)
  rw [ambientChartEvaluation_ker]
  exact Ideal.subset_span (Set.mem_singleton _)

/- Generic ring-hom evaluation of the genuine corrected vector. Separating
this elementary identity avoids repeated unfolding of the actual projective
localization while traversing polynomial ideal membership proofs. -/
private theorem ringHom_corrected_vector_evaluate
    {ι : Type u} {B : Type u} [CommRing B] (f : A →+* B)
    (s : A) (hs : f s = 0) (c b : ι → A) :
    (fun i => f ((c - s • b) i)) = fun i => f (c i) := by
  funext i
  change f (c i - s * b i) = f (c i)
  rw [map_sub, map_mul, hs, zero_mul, sub_zero]

/- Forward exactness: surjectivity gives literal polynomial lifts; the
original homogeneous correction and original syzygies give a literal relation
preimage; actual evaluation kills only X_j-1. -/
private theorem actualDegreeZeroChart_kernel_has_relation_preimage
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (j : Fin 4) (x : ι → HomogeneousLocalization.Away PS (X j))
    (hx : actualDegreeZeroChartGeneratorMap j g x = 0) :
    ∃ b : κ → HomogeneousLocalization.Away PS (X j),
      actualDegreeZeroChartRelationMap j r b = x := by
  classical
  let f : A →+* HomogeneousLocalization.Away PS (X j) := ambientChartEvaluation j
  have hf : Function.Surjective f := ambientChartEvaluation_surjective j
  have hpre : ∀ i, ∃ c : A, f c = x i := fun i => hf (x i)
  choose c hc using hpre
  have hzero : f (actualPolynomialGeneratorMap g c) = 0 :=
    (actualDegreeZeroChartGeneratorMap_evaluate j g c).symm.trans
      ((congrArg (actualDegreeZeroChartGeneratorMap j g) (funext hc)).trans hx)
  have hmem : actualPolynomialGeneratorMap g c ∈
      Ideal.span ({(X j : A) - 1} : Set A) := by
    change actualPolynomialGeneratorMap g c ∈ RingHom.ker f at hzero
    simpa only [f, ambientChartEvaluation_ker, ambientChartPresentationIdeal] using hzero
  obtain ⟨b, t, hRt⟩ := actualPolynomialPresentation_coordinate_correction I g r hg hr j c hmem
  have heval := ringHom_corrected_vector_evaluate f ((X j : A) - 1)
    (actualAmbientChartEvaluation_coordinate_sub_one j) c b
  have hrelEval := congrArg (fun v : ι → A => fun i => f (v i)) hRt
  exact ⟨fun a => f (t a),
    (actualDegreeZeroChartRelationMap_evaluate j r t).trans
      (hrelEval.trans (heval.trans (funext hc)))⟩

/- Reverse exactness: a literal lifted relation has zero polynomial generator
value, and actual evaluation preserves that SAME identity. -/
private theorem actualDegreeZeroChart_relation_generator_zero
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (j : Fin 4) (b : κ → HomogeneousLocalization.Away PS (X j)) :
    actualDegreeZeroChartGeneratorMap j g (actualDegreeZeroChartRelationMap j r b) = 0 := by
  classical
  let f : A →+* HomogeneousLocalization.Away PS (X j) := ambientChartEvaluation j
  have hf : Function.Surjective f := ambientChartEvaluation_surjective j
  have hpre : ∀ a, ∃ t : A, f t = b a := fun a => hf (b a)
  choose t ht using hpre
  have hR : actualDegreeZeroChartRelationMap j r b =
      fun i => f (actualPolynomialRelationMap r t i) :=
    (congrArg (actualDegreeZeroChartRelationMap j r) (funext ht)).symm.trans
      (actualDegreeZeroChartRelationMap_evaluate j r t)
  have hGR : actualPolynomialGeneratorMap g (actualPolynomialRelationMap r t) = 0 :=
    (actualPolynomialRelationMap_generatorMap_exact g r hr
      (actualPolynomialRelationMap r t)).mpr ⟨t, rfl⟩
  exact (congrArg (actualDegreeZeroChartGeneratorMap j g) hR).trans
    ((actualDegreeZeroChartGeneratorMap_evaluate j g (actualPolynomialRelationMap r t)).trans
      ((congrArg (fun a : A => f a) hGR).trans (map_zero f)))

/-- The OWN homogeneous presentation remains exact in its actual
DEGREE-ZERO projective coordinate chart. No chart exactness, saturation,
flat specialization, or desired kernel comparison is an input. -/
theorem actualDegreeZeroChartPresentation_exact
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → A) (r : κ → ι → A)
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (j : Fin 4) :
    Function.Exact (actualDegreeZeroChartRelationMap j r)
      (actualDegreeZeroChartGeneratorMap j g) := by
  intro x
  constructor
  · intro hx
    exact actualDegreeZeroChart_kernel_has_relation_preimage I g r hg hr j x hx
  · rintro ⟨b, rfl⟩
    exact actualDegreeZeroChart_relation_generator_zero g r hr j b

/-- The image is the SAME scheme-theoretic quotient-chart kernel, retaining
all of the OWN homogeneous ideal, including its nilpotents. -/
theorem actualDegreeZeroChartGeneratorMap_range_eq_quotientKernel
    (I : HomogeneousIdeal PS) {ι : Type u} [Fintype ι]
    (g : ι → A) (hg : Ideal.span (Set.range g) = I.toIdeal) (j : Fin 4) :
    (actualDegreeZeroChartGeneratorMap j g).range =
      RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j) := by
  classical
  have hspan : (actualDegreeZeroChartGeneratorMap j g).range =
      Ideal.span (Set.range (fun i => ambientChartEvaluation j (g i))) := by
    ext z
    change (∃ c, actualDegreeZeroChartGeneratorMap j g c = z) ↔ _
    change (∃ c : ι → HomogeneousLocalization.Away PS (X j),
      (∑ i, ambientChartEvaluation j (g i) * c i) = z) ↔ _
    simpa only [mul_comm] using
      (Ideal.mem_span_range_iff_exists_fun (v := fun i => ambientChartEvaluation j (g i))
        (x := z)).symm
  rw [hspan, PfaffianDescent.quotientAmbientChartMap_ker_eq_ideal_image, ← hg,
    Ideal.map_span, ← Set.range_comp']

/-- Original K coefficients enter through the OWN chart base homomorphism;
linearity is inherited from the unchanged chart ring module action. -/
theorem actualDegreeZeroChartGeneratorMap_ground_smul
    {ι : Type u} [Fintype ι] (j : Fin 4) (g : ι → A)
    (c : K) (x : ι → HomogeneousLocalization.Away PS (X j)) :
    actualDegreeZeroChartGeneratorMap j g
        ((AllCharacteristics.GradedChart.baseMap PS (z := X j) c) • x) =
      (AllCharacteristics.GradedChart.baseMap PS (z := X j) c) •
        actualDegreeZeroChartGeneratorMap j g x :=
  (actualDegreeZeroChartGeneratorMap j g).map_smul _ _

/-- A primitive OWN homogeneous ideal internally supplies finite homogeneous
matrices with genuine exactness and the SAME actual quotient kernel on
EVERY native projective coordinate chart. -/
theorem homogeneousIdeal_exists_actualDegreeZeroChartPresentation
    (I : HomogeneousIdeal PS) :
    ∃ (T : Finset A) (d : T → ℕ) (R : Finset (T → A)) (e : R → ℕ) (B : ℕ),
      Ideal.span (T : Set A) = I.toIdeal ∧
      (∀ i : T, d i ≤ B ∧ (i : A).IsHomogeneous (d i)) ∧
      (∀ a : R, e a ≤ B ∧ ActualWeightedPolynomialHomogeneous d (e a) a.val) ∧
      ∀ j : Fin 4,
        Function.Exact (actualDegreeZeroChartRelationMap j (fun a : R => a.val))
          (actualDegreeZeroChartGeneratorMap j (fun i : T => i.val)) ∧
        (actualDegreeZeroChartGeneratorMap j (fun i : T => i.val)).range =
          RingHom.ker (PfaffianDescent.quotientAmbientChartMap I j) := by
  classical
  obtain ⟨T, d, R, e, B, hT, hd, hR, he⟩ :=
    homogeneousIdeal_exists_actual_finite_homogeneousPresentation_and_relations I
  have hTset : Set.range (fun i : T => i.val) = (T : Set A) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact i.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  have hRset : Set.range (fun a : R => a.val) = (R : Set (T → A)) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact i.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  have hg : Ideal.span (Set.range (fun i : T => i.val)) = I.toIdeal := by
    rw [hTset]
    exact hT
  have hr : Submodule.span A (Set.range (fun a : R => a.val)) =
      (actualPolynomialGeneratorMap (fun i : T => i.val)).ker := by
    rw [hRset]
    exact hR
  refine ⟨T, d, R, e, B, hT, hd, he, fun j => ?_⟩
  exact ⟨actualDegreeZeroChartPresentation_exact I (fun i : T => i.val)
      (fun a : R => a.val) hg hr j,
    actualDegreeZeroChartGeneratorMap_range_eq_quotientKernel I (fun i : T => i.val) hg j⟩

end PfaffianDescent.Coray

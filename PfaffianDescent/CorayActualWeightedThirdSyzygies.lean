import PfaffianDescent.CorayActualPresentationNativeLocalizationSheafExact

/-! A third finite weighted polynomial term for the SAME whole ideal.
Source only, UNVERIFIED. No compiler or project mutation by the author.
The final ideal caller constructs every matrix and weight internally. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K

/-- Multiplying the i-th weighted row by X₀^(d i) turns it into an
ordinary homogeneous scalar generator family of the SOURCE weights e. -/
theorem actualWeightedRelation_liftedRow_isHomogeneous
    {ι κ : Type u} (d : ι → ℕ) (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (i : ι) (a : κ) :
    ((X (0 : Fin 4) : A) ^ d i * r a i).IsHomogeneous (e a) := by
  by_cases hi : d i ≤ e a
  · have h := (isHomogeneous_X_pow (0 : Fin 4) (d i)).mul (hr a i).1
    have hindex : d i + (e a - d i) = e a := by omega
    simpa only [hindex] using h
  · rw [(hr a i).2 (Nat.lt_of_not_ge hi), mul_zero]
    exact MvPolynomial.isHomogeneous_zero (Fin 4) K (e a)

/-- Literal row factorization; this does not replace either polynomial map. -/
theorem actualWeightedRelation_liftedRow_apply
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (r : κ → ι → A) (i : ι) (c : κ → A) :
    actualPolynomialGeneratorMap (fun a => (X (0 : Fin 4) : A) ^ d i * r a i) c =
      (X (0 : Fin 4) : A) ^ d i * actualPolynomialRelationMap r c i := by
  classical
  change (∑ a, ((X (0 : Fin 4) : A) ^ d i * r a i) * c a) =
    (X (0 : Fin 4) : A) ^ d i * (∑ a, c a • r a) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact (mul_assoc ((X (0 : Fin 4) : A) ^ d i) (r a i) (c a)).trans
    (congrArg (fun q : A => (X (0 : Fin 4) : A) ^ d i * q) (mul_comm (r a i) (c a)))

/-- The actual MATRIX kernel, not a scalar substitute, is stable under
its source weighted degree projections. Polynomial-domain cancellation
removes the row factors after the accepted scalar projection theorem. -/
theorem actualPolynomialRelationMap_kernel_weightedComponent
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (m : ℕ) (c : κ → A) (hc : c ∈ (actualPolynomialRelationMap r).ker) :
    actualWeightedPolynomialComponent e m c ∈ (actualPolynomialRelationMap r).ker := by
  apply LinearMap.mem_ker.mpr
  funext i
  let g : κ → A := fun a => (X (0 : Fin 4) : A) ^ d i * r a i
  have hg : ∀ a, (g a).IsHomogeneous (e a) :=
    actualWeightedRelation_liftedRow_isHomogeneous d r e hr i
  have hzero : actualPolynomialGeneratorMap g c = 0 := by
    rw [actualWeightedRelation_liftedRow_apply d r i c, LinearMap.mem_ker.mp hc]
    simp only [Pi.zero_apply, mul_zero]
  have hcomponent : actualPolynomialGeneratorMap g
      (actualWeightedPolynomialComponent e m c) = 0 := by
    rw [actualPolynomialGeneratorMap_weightedComponent g e hg m c, hzero, map_zero]
  have hproduct : (X (0 : Fin 4) : A) ^ d i *
      actualPolynomialRelationMap r (actualWeightedPolynomialComponent e m c) i = 0 :=
    (actualWeightedRelation_liftedRow_apply d r i _).symm.trans hcomponent
  exact (mul_eq_zero.mp hproduct).resolve_left
    (pow_ne_zero (d i) (MvPolynomial.X_ne_zero (0 : Fin 4)))

/-- Noetherianity constructs finite homogeneous generators of the SAME
second relation kernel. The matrix homogeneity is natural input; its
kernel stability and finite generation are proved here. -/
theorem actualPolynomialRelationMap_kernel_exists_bounded_homogeneousGenerators
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (d : ι → ℕ) (r : κ → ι → A) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a)) :
    ∃ (S : Finset (κ → A)) (f : S → ℕ) (B : ℕ),
      Submodule.span A (S : Set (κ → A)) = (actualPolynomialRelationMap r).ker ∧
      ∀ s : S, f s ≤ B ∧ ActualWeightedPolynomialHomogeneous e (f s) s.val := by
  apply actualWeightedPolynomialSubmodule_exists_bounded_homogeneousGenerators e
    (actualPolynomialRelationMap r).ker
  exact actualPolynomialRelationMap_kernel_weightedComponent d r e hr

/-- A whole homogeneous ideal internally supplies THREE finite weighted
polynomial terms: generators, their relations, and relations of those
relations. Both displayed kernels belong to the literal existing maps.
There is no supplied third presentation, desired vanishing or resolution. -/
theorem homogeneousIdeal_exists_actual_finite_homogeneousThreeTermPresentation
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    ∃ (T : Finset A) (d : T → ℕ) (R : Finset (T → A)) (e : R → ℕ)
      (S : Finset (R → A)) (f : S → ℕ) (B : ℕ),
      Ideal.span (T : Set A) = I.toIdeal ∧
      (∀ i : T, d i ≤ B ∧ (i : A).IsHomogeneous (d i)) ∧
      Submodule.span A (R : Set (T → A)) =
        (actualPolynomialGeneratorMap (fun i : T => i.val)).ker ∧
      (∀ a : R, e a ≤ B ∧ ActualWeightedPolynomialHomogeneous d (e a) a.val) ∧
      Submodule.span A (S : Set (R → A)) =
        (actualPolynomialRelationMap (fun a : R => a.val)).ker ∧
      (∀ s : S, f s ≤ B ∧ ActualWeightedPolynomialHomogeneous e (f s) s.val) := by
  classical
  obtain ⟨T, d, R, e, B, hI, hd, hR, he⟩ :=
    homogeneousIdeal_exists_actual_finite_homogeneousPresentation_and_relations I
  obtain ⟨S, f, C, hS, hf⟩ :=
    actualPolynomialRelationMap_kernel_exists_bounded_homogeneousGenerators
      d (fun a : R => a.val) e (fun a => (he a).2)
  refine ⟨T, d, R, e, S, f, max B C, hI, ?_, hR, ?_, hS, ?_⟩
  · intro i
    exact ⟨(hd i).1.trans (le_max_left B C), (hd i).2⟩
  · intro a
    exact ⟨(he a).1.trans (le_max_left B C), (he a).2⟩
  · intro s
    exact ⟨(hf s).1.trans (le_max_right B C), (hf s).2⟩

end PfaffianDescent.Coray

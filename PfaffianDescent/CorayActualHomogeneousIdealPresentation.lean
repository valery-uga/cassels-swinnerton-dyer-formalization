import PfaffianDescent.CorayNoetherianCoordinateTorsionBound
import PfaffianDescent.HomogeneousProjection
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Lean.Elab.Tactic.Omega

/-! Literal homogeneous ideal presentation and its actual relation kernel.
The primitive caller constructs every generator, degree and finite kernel
internally. No sheaf section surjectivity or H1 certificate is assumed.
SOURCE ONLY UNVERIFIED; root owns all compiler/audit checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u v
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal polynomial-linear free presentation map, with original
polynomial multiplication and standard coefficient actions. -/
def actualPolynomialGeneratorMap
    {ι : Type v} [Fintype ι] (g : ι → MvPolynomial (Fin 4) K) :
    (ι → MvPolynomial (Fin 4) K) →ₗ[MvPolynomial (Fin 4) K]
      MvPolynomial (Fin 4) K where
  toFun c := ∑ i, g i * c i
  map_add' c e := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_left_comm (g i) r (c i)

/-- The actual relation kernel is finite over the OWN polynomial ring,
derived from finite source rank and polynomial Noetherianity. -/
theorem actualPolynomialGeneratorMap_kernel_finite
    {ι : Type v} [Fintype ι] (g : ι → MvPolynomial (Fin 4) K) :
    Module.Finite (MvPolynomial (Fin 4) K) (actualPolynomialGeneratorMap g).ker := by
  infer_instance

/-- Complementary-degree projection commutes with the SAME actual generator
map at every degree above the generator weights. -/
theorem actualPolynomialGeneratorMap_homogeneousComponent
    {ι : Type v} [Fintype ι] (g : ι → MvPolynomial (Fin 4) K)
    (d : ι → ℕ) (hhom : ∀ i, (g i).IsHomogeneous (d i))
    (m : ℕ) (hbound : ∀ i, d i ≤ m) (c : ι → MvPolynomial (Fin 4) K) :
    actualPolynomialGeneratorMap g
        (fun i => homogeneousComponent (m - d i) (c i)) =
      homogeneousComponent m (actualPolynomialGeneratorMap g c) := by
  change (∑ i, g i * homogeneousComponent (m - d i) (c i)) =
    homogeneousComponent m (∑ i, g i * c i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi := hbound i
  have hindex : d i + (m - d i) = m := by omega
  have hmul := PfaffianDescent.homogeneousComponent_mul_left (q := c i) (hhom i) (m - d i)
  rw [hindex] at hmul
  exact hmul.symm

/-- Actual homogeneous projection preserves the actual relation kernel;
relations are not replaced by unrelated kernel certificates. -/
theorem actualPolynomialGeneratorMap_relation_homogeneousComponent
    {ι : Type v} [Fintype ι] (g : ι → MvPolynomial (Fin 4) K)
    (d : ι → ℕ) (hhom : ∀ i, (g i).IsHomogeneous (d i))
    (m : ℕ) (hbound : ∀ i, d i ≤ m)
    (c : (actualPolynomialGeneratorMap g).ker) :
    (fun i => homogeneousComponent (m - d i) (c.val i)) ∈
      (actualPolynomialGeneratorMap g).ker := by
  apply LinearMap.mem_ker.mpr
  rw [actualPolynomialGeneratorMap_homogeneousComponent g d hhom m hbound,
    LinearMap.mem_ker.mp c.property, map_zero]

/-- Every SAME-degree element in the literal generator ideal has an actual
weighted homogeneous polynomial preimage. Only natural generator data occur
in this generic algebra lemma; the primitive ideal caller derives them. -/
theorem actualPolynomialGeneratorMap_homogeneous_preimage
    {ι : Type v} [Fintype ι] (g : ι → MvPolynomial (Fin 4) K)
    (d : ι → ℕ) (hhom : ∀ i, (g i).IsHomogeneous (d i))
    (m : ℕ) (hbound : ∀ i, d i ≤ m)
    (a : homogeneousSubmodule (Fin 4) K m)
    (ha : (a : MvPolynomial (Fin 4) K) ∈ Ideal.span (Set.range g)) :
    ∃ c : ι → MvPolynomial (Fin 4) K,
      (∀ i, (c i).IsHomogeneous (m - d i)) ∧
      actualPolynomialGeneratorMap g c = (a : MvPolynomial (Fin 4) K) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
  have hmap : actualPolynomialGeneratorMap g c = (a : MvPolynomial (Fin 4) K) := by
    change (∑ i, g i * c i) = (a : MvPolynomial (Fin 4) K)
    simpa only [mul_comm] using hc
  refine ⟨fun i => homogeneousComponent (m - d i) (c i),
    fun i => homogeneousComponent_isHomogeneous _ _, ?_⟩
  rw [actualPolynomialGeneratorMap_homogeneousComponent g d hhom m hbound,
    hmap, homogeneousComponent_eq_self a.property]

/-- The OWN homogeneous ideal has an internally constructed finite free
polynomial presentation, a derived degree bound, a genuinely finite SAME
relation kernel, and actual degreewise homogeneous surjection above that
bound. No supplied generator, presentation, finite-kernel, high-degree
section/cohomology comparison, or Serre conclusion is an input. -/
theorem homogeneousIdeal_exists_actual_bounded_homogeneousPresentation
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    ∃ (T : Finset (MvPolynomial (Fin 4) K)) (d : T → ℕ) (N : ℕ),
      Ideal.span (T : Set (MvPolynomial (Fin 4) K)) = I.toIdeal ∧
      (∀ i : T, (i : MvPolynomial (Fin 4) K).IsHomogeneous (d i)) ∧
      Module.Finite (MvPolynomial (Fin 4) K)
        (actualPolynomialGeneratorMap (fun i : T => (i : MvPolynomial (Fin 4) K))).ker ∧
      ∀ m : ℕ, N ≤ m → ∀ a : homogeneousSubmodule (Fin 4) K m,
        (a : MvPolynomial (Fin 4) K) ∈ I.toIdeal →
        ∃ c : T → MvPolynomial (Fin 4) K,
          (∀ i : T, (c i).IsHomogeneous (m - d i)) ∧
          actualPolynomialGeneratorMap
            (fun i : T => (i : MvPolynomial (Fin 4) K)) c =
            (a : MvPolynomial (Fin 4) K) := by
  classical
  obtain ⟨T, N, hspan, hgen⟩ :=
    homogeneousIdeal_exists_finite_homogeneousGenerators_with_degreeBound I
  have hgen' : ∀ i : T, ∃ d : ℕ,
      d ≤ N ∧ (i : MvPolynomial (Fin 4) K).IsHomogeneous d :=
    fun i => hgen i.val i.property
  choose d hd using hgen'
  let g : T → MvPolynomial (Fin 4) K := fun i => i.val
  have hrange : Set.range g = (T : Set (MvPolynomial (Fin 4) K)) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact i.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  refine ⟨T, d, N, hspan, fun i => (hd i).2,
    actualPolynomialGeneratorMap_kernel_finite g, ?_⟩
  intro m hm a ha
  apply actualPolynomialGeneratorMap_homogeneous_preimage g d
    (fun i => (hd i).2) m (fun i => (hd i).1.trans hm) a
  rwa [hrange, hspan]

end PfaffianDescent.Coray

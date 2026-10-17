/- SOURCE ONLY / UNCHECKED: native signed degree shifts and exact supported range in three-coordinate homogeneous localizations. -/
import PfaffianDescent.PlaneLaurentLocalization

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped AddMonoidAlgebra BigOperators
universe u
namespace PfaffianDescent.PlaneTwistLaurent

open PlaneLaurentLocalization

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K

abbrev LaurentExponent := PlaneLaurentLocalization.LaurentExponent
abbrev LaurentPolynomial := PlaneLaurentLocalization.LaurentPolynomial K

def coordinateExponent (i : Fin 3) : LaurentExponent :=
  Finsupp.single i 1

def twistShift (m : ℕ) (i : Fin 3) : LaurentExponent :=
  -(m • coordinateExponent i)

def twistAwayToLaurent
    (m n : ℕ) (f : Fin (n + 1) → Fin 3) :
    HomogeneousLocalization.Away PS
        (ProjectivePlaneNative.p2CechDenominator (K := K) n f) →+
      LaurentPolynomial K where
  toFun z := awayToLaurent (K := K) n f z *
    AddMonoidAlgebra.single (twistShift m (f 0)) 1
  map_zero' := by simp
  map_add' x y := by simp [add_mul]

lemma mul_single_mem_support_iff
    (g : LaurentPolynomial K) (s a : LaurentExponent) :
    a ∈ (g * AddMonoidAlgebra.single s 1).coeff.support ↔
      ∃ b ∈ g.coeff.support, b + s = a := by
  rw [AddMonoidAlgebra.support_coeff_mul_single _ _ (by simp)]
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, by rw [addRightEmbedding_apply]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, by rw [addRightEmbedding_apply]⟩

lemma totalDegree_coordinateExponent (i : Fin 3) :
    totalDegree (coordinateExponent i) = 1 := by
  unfold PlaneLaurentLocalization.totalDegree coordinateExponent
  simp

lemma totalDegree_twistShift (m : ℕ) (i : Fin 3) :
    totalDegree (twistShift m i) = -(m : ℤ) := by
  rw [twistShift, totalDegree_neg, totalDegree_nsmul,
    totalDegree_coordinateExponent]
  simp

lemma twistAwayToLaurent_injective
    (m n : ℕ) (f : Fin (n + 1) → Fin 3) :
    Function.Injective (twistAwayToLaurent (K := K) m n f) := by
  intro x y h
  apply awayToLaurent_injective (K := K) n f
  exact (isUnit_single_one (K := K) (twistShift m (f 0))).mul_right_cancel h

lemma negativeSupport_add_twistShift_subset
    (n m : ℕ) (f : Fin (n + 1) → Fin 3) (b : LaurentExponent)
    (hb : negativeSupport b ⊆ Set.range f) :
    negativeSupport (b + twistShift m (f 0)) ⊆ Set.range f := by
  intro i hi
  by_cases hir : i ∈ Set.range f
  · exact hir
  · have hne : i ≠ f 0 := by
      intro h
      apply hir
      exact ⟨0, h.symm⟩
    have hbnonneg : 0 ≤ b i := le_of_not_gt (fun h => hir (hb h))
    change (b + twistShift m (f 0)) i < 0 at hi
    simp [twistShift, coordinateExponent, hne] at hi
    omega

lemma twistAwayToLaurent_support_properties
    (m n : ℕ) (f : Fin (n + 1) → Fin 3)
    (z : HomogeneousLocalization.Away PS
      (ProjectivePlaneNative.p2CechDenominator (K := K) n f)) :
    ∀ a ∈ (twistAwayToLaurent (K := K) m n f z).coeff.support,
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ :=
    (mul_single_mem_support_iff (K := K)
      (awayToLaurent (K := K) n f z) (twistShift m (f 0)) a).mp ha
  have hbase := awayToLaurent_support_properties (K := K) n f z b hb
  constructor
  · rw [totalDegree_add, hbase.1, totalDegree_twistShift]
    simp
  · exact negativeSupport_add_twistShift_subset n m f b hbase.2

def positiveTwistShift (m : ℕ) (i : Fin 3) : LaurentExponent :=
  m • coordinateExponent i

lemma totalDegree_positiveTwistShift (m : ℕ) (i : Fin 3) :
    totalDegree (positiveTwistShift m i) = (m : ℤ) := by
  rw [positiveTwistShift, totalDegree_nsmul, totalDegree_coordinateExponent]
  simp

lemma negativeSupport_add_positiveTwistShift_subset
    (m : ℕ) (i : Fin 3) (b : LaurentExponent) :
    negativeSupport (b + positiveTwistShift m i) ⊆ negativeSupport b := by
  intro j hj
  change (b + positiveTwistShift m i) j < 0 at hj
  change b j < 0
  simp only [Finsupp.add_apply, positiveTwistShift, Finsupp.smul_apply,
    nsmul_eq_mul, coordinateExponent] at hj
  by_cases hji : j = i
  · subst j
    simp only [Finsupp.single_eq_same, mul_one] at hj
    omega
  · rw [Finsupp.single_eq_of_ne hji] at hj
    simp only [mul_zero, add_zero] at hj
    exact hj

lemma exists_twistAwayToLaurent_eq_of_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 3) (g : LaurentPolynomial K)
    (hg : ∀ a ∈ g.coeff.support,
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f) :
    ∃ z : HomogeneousLocalization.Away PS
        (ProjectivePlaneNative.p2CechDenominator (K := K) n f),
      twistAwayToLaurent (K := K) m n f z = g := by
  let gpos := g * AddMonoidAlgebra.single (positiveTwistShift m (f 0)) 1
  have hgpos : ∀ a ∈ gpos.coeff.support,
      totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ :=
      (mul_single_mem_support_iff (K := K) g (positiveTwistShift m (f 0)) a).mp ha
    have hbase := hg b hb
    constructor
    · rw [totalDegree_add, hbase.1, totalDegree_positiveTwistShift]
      simp
    · exact (negativeSupport_add_positiveTwistShift_subset m (f 0) b).trans hbase.2
  obtain ⟨z, hz⟩ :=
    exists_awayToLaurent_eq_of_support (K := K) n f gpos hgpos
  refine ⟨z, ?_⟩
  change awayToLaurent (K := K) n f z *
      AddMonoidAlgebra.single (twistShift m (f 0)) 1 = g
  rw [hz]
  change (g * AddMonoidAlgebra.single (positiveTwistShift m (f 0)) 1) *
      AddMonoidAlgebra.single (twistShift m (f 0)) 1 = g
  rw [mul_assoc, AddMonoidAlgebra.single_mul_single]
  have hshift : positiveTwistShift m (f 0) + twistShift m (f 0) = 0 := by
    simp [positiveTwistShift, twistShift]
  rw [hshift]
  simp only [← AddMonoidAlgebra.one_def, mul_one]

lemma positiveTwistShift_mul_twistShift (m : ℕ) (k : Fin 3) :
    AddMonoidAlgebra.single (positiveTwistShift m k) (1 : K) *
      AddMonoidAlgebra.single (twistShift m k) 1 = 1 := by
  rw [AddMonoidAlgebra.single_mul_single]
  simp [positiveTwistShift, twistShift, AddMonoidAlgebra.one_def]

lemma twistShift_mul_positiveTwistShift (m : ℕ) (k : Fin 3) :
    AddMonoidAlgebra.single (twistShift m k) (1 : K) *
      AddMonoidAlgebra.single (positiveTwistShift m k) 1 = 1 := by
  rw [mul_comm, positiveTwistShift_mul_twistShift K m k]


end PfaffianDescent.PlaneTwistLaurent

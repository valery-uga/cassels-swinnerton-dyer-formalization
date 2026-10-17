/- SOURCE ONLY / UNCHECKED: actual Fin3 homogeneous-localization Laurent embedding and supported range, with literal original coordinate products. -/
import PfaffianDescent.PlaneNativeCechCover
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Homogeneous localizations as Laurent polynomials

This file embeds every homogeneous degree-zero localization occurring in the
standard three-chart Cech complex of projective plane into a common
finitely supported Laurent polynomial ring.  The common target is the
coefficient model used by `VoisinLaurentCechCore`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open MvPolynomial
open scoped AddMonoidAlgebra BigOperators

universe u

namespace PfaffianDescent
namespace PlaneLaurentLocalization

variable (K : Type u) [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => MvPolynomial (Fin 3) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K

abbrev LaurentExponent := Fin 3 →₀ ℤ
abbrev LaurentPolynomial := AddMonoidAlgebra K LaurentExponent

def exponentToInt : (Fin 3 →₀ ℕ) →+ LaurentExponent :=
  Finsupp.mapRange.addMonoidHom Int.ofNatHom.toAddMonoidHom

lemma exponentToInt_apply (a : Fin 3 →₀ ℕ) (i : Fin 3) :
    exponentToInt a i = (a i : ℤ) := by
  rfl

lemma exponentToInt_injective : Function.Injective exponentToInt := by
  intro a b h
  apply Finsupp.ext
  intro i
  have hi := congrArg (fun q : LaurentExponent => q i) h
  change (a i : ℤ) = (b i : ℤ) at hi
  exact Int.ofNat_inj.mp hi

def polynomialToLaurent : S →+* LaurentPolynomial K :=
  AddMonoidAlgebra.mapDomainRingHom K exponentToInt

lemma polynomialToLaurent_injective :
    Function.Injective (polynomialToLaurent (K := K)) := by
  change Function.Injective (AddMonoidAlgebra.mapDomain exponentToInt)
  exact AddMonoidAlgebra.mapDomain_injective exponentToInt_injective

/-- The exponent vector of the product of coordinates in an ordered Cech
intersection. -/
def cechExponent (n : ℕ) (f : Fin (n + 1) → Fin 3) : LaurentExponent :=
  ∑ a, Finsupp.single (f a) 1

lemma cechExponent_apply (n : ℕ) (f : Fin (n + 1) → Fin 3) (i : Fin 3) :
    cechExponent n f i =
      ((Finset.univ.filter fun a => f a = i).card : ℤ) := by
  rw [cechExponent, Finsupp.finsetSum_apply]
  simpa only [Finsupp.single_apply] using
    (Finset.sum_boole (R := ℤ) (fun a => f a = i) Finset.univ)

lemma cechExponent_pos_iff (n : ℕ) (f : Fin (n + 1) → Fin 3) (i : Fin 3) :
    0 < cechExponent n f i ↔ i ∈ Set.range f := by
  rw [cechExponent_apply]
  norm_cast
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and, Set.mem_range]

lemma cechExponent_nonneg (n : ℕ) (f : Fin (n + 1) → Fin 3) (i : Fin 3) :
    0 ≤ cechExponent n f i := by
  rw [cechExponent_apply]
  exact Int.natCast_nonneg _

lemma cechExponent_sum (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    ∑ i, cechExponent n f i = (n + 1 : ℕ) := by
  simp only [cechExponent, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp

lemma polynomialToLaurent_X (i : Fin 3) :
    polynomialToLaurent (K := K) (MvPolynomial.X i) =
      AddMonoidAlgebra.single (Finsupp.single i 1) 1 := by
  change AddMonoidAlgebra.mapDomain exponentToInt
      (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  congr
  ext j
  simp [exponentToInt]

lemma polynomialToLaurent_cechDenominator
    (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    polynomialToLaurent (K := K) (ProjectivePlaneNative.p2CechDenominator (K := K) n f) =
      AddMonoidAlgebra.single (cechExponent n f) 1 := by
  simp only [ProjectivePlaneNative.p2CechDenominator, map_prod,
    polynomialToLaurent_X]
  have aux : ∀ s : Finset (Fin (n + 1)),
      (∏ a ∈ s, AddMonoidAlgebra.single
        (Finsupp.single (f a) (1 : ℤ) : LaurentExponent) (1 : K)) =
        AddMonoidAlgebra.single
          (∑ a ∈ s, (Finsupp.single (f a) (1 : ℤ) : LaurentExponent)) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, AddMonoidAlgebra.one_def]
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
          AddMonoidAlgebra.single_mul_single, one_mul]
  simpa only [cechExponent] using aux Finset.univ

lemma isUnit_single_one (a : LaurentExponent) :
    IsUnit (AddMonoidAlgebra.single a (1 : K)) := by
  apply IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-a) (1 : K))
  rw [AddMonoidAlgebra.single_mul_single]
  simp only [add_neg_cancel, one_mul, ← AddMonoidAlgebra.one_def]

lemma polynomialToLaurent_cechDenominator_isUnit
    (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    IsUnit (polynomialToLaurent (K := K) (ProjectivePlaneNative.p2CechDenominator (K := K) n f)) := by
  rw [polynomialToLaurent_cechDenominator]
  exact isUnit_single_one (K := K) _

/-- Extend the polynomial-to-Laurent embedding across localization at a
Cech denominator. -/
def localizationAwayToLaurent (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    Localization.Away (ProjectivePlaneNative.p2CechDenominator (K := K) n f) →+* LaurentPolynomial K :=
  IsLocalization.Away.lift (ProjectivePlaneNative.p2CechDenominator (K := K) n f)
    (polynomialToLaurent_cechDenominator_isUnit (K := K) n f)

lemma localizationAwayToLaurent_algebraMap
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (x : S) :
    localizationAwayToLaurent (K := K) n f
        (algebraMap S (Localization.Away (ProjectivePlaneNative.p2CechDenominator (K := K) n f)) x) =
      polynomialToLaurent (K := K) x := by
  exact IsLocalization.Away.lift_eq _ _ _

lemma localizationAwayToLaurent_injective
    (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    Function.Injective (localizationAwayToLaurent (K := K) n f) := by
  unfold localizationAwayToLaurent IsLocalization.Away.lift
  rw [IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    have h' := congrArg (localizationAwayToLaurent (K := K) n f) h
    simpa only [localizationAwayToLaurent_algebraMap] using h'
  · intro h
    have hxy : x = y := polynomialToLaurent_injective (K := K) h
    exact congrArg (algebraMap S
      (Localization.Away (ProjectivePlaneNative.p2CechDenominator (K := K) n f))) hxy

/-- Send a homogeneous degree-zero fraction on a Cech intersection to its
Laurent expansion. -/
def awayToLaurent (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    HomogeneousLocalization.Away PS (ProjectivePlaneNative.p2CechDenominator (K := K) n f) →+*
      LaurentPolynomial K :=
  (localizationAwayToLaurent (K := K) n f).comp
    (algebraMap
      (HomogeneousLocalization.Away PS (ProjectivePlaneNative.p2CechDenominator (K := K) n f))
      (Localization.Away (ProjectivePlaneNative.p2CechDenominator (K := K) n f)))

lemma awayToLaurent_injective (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    Function.Injective (awayToLaurent (K := K) n f) :=
  (localizationAwayToLaurent_injective (K := K) n f).comp
    (HomogeneousLocalization.val_injective _)

lemma single_neg_nsmul_mul_single_pow (a : LaurentExponent) (r : ℕ) :
    AddMonoidAlgebra.single (- (r • a)) (1 : K) *
        (AddMonoidAlgebra.single a (1 : K)) ^ r = 1 := by
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]
  simp only [one_pow, neg_add_cancel, one_mul, ← AddMonoidAlgebra.one_def]

/-- On a standard representative `p / d^r`, the common Laurent embedding
subtracts `r` copies of the Cech denominator exponent from every numerator
monomial. -/
lemma awayToLaurent_mk
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (r : ℕ) (p : S)
    (hp : p ∈ PS (r • (n + 1))) :
    awayToLaurent (K := K) n f
        (HomogeneousLocalization.Away.mk PS
          (ProjectivePlaneNative.p2CechDenominator_mem (K := K) n f)
          r p hp) =
      polynomialToLaurent (K := K) p *
        AddMonoidAlgebra.single (- (r • cechExponent n f)) 1 := by
  let d := ProjectivePlaneNative.p2CechDenominator (K := K) n f
  let D := polynomialToLaurent (K := K) d
  have hD : D = AddMonoidAlgebra.single (cechExponent n f) 1 := by
    exact polynomialToLaurent_cechDenominator (K := K) n f
  have hDunit : IsUnit D := by
    exact polynomialToLaurent_cechDenominator_isUnit (K := K) n f
  apply (hDunit.pow r).mul_left_cancel
  have hspec := IsLocalization.mk'_spec
    (Localization.Away d) p
    (show Submonoid.powers d from ⟨d ^ r, ⟨r, rfl⟩⟩)
  have hmapped := congrArg (localizationAwayToLaurent (K := K) n f) hspec
  change D ^ r *
      awayToLaurent (K := K) n f
        (HomogeneousLocalization.Away.mk PS
          (ProjectivePlaneNative.p2CechDenominator_mem (K := K) n f)
          r p hp) =
    D ^ r * (polynomialToLaurent (K := K) p *
      AddMonoidAlgebra.single (- (r • cechExponent n f)) 1)
  have hinv :
      AddMonoidAlgebra.single (- (r • cechExponent n f)) (1 : K) * D ^ r = 1 := by
    rw [hD]
    exact single_neg_nsmul_mul_single_pow (K := K) _ _
  have hright :
      D ^ r * (polynomialToLaurent (K := K) p *
        AddMonoidAlgebra.single (- (r • cechExponent n f)) 1) =
        polynomialToLaurent (K := K) p := by
    calc
      _ = polynomialToLaurent (K := K) p *
          (AddMonoidAlgebra.single (- (r • cechExponent n f)) 1 * D ^ r) := by
            ac_rfl
      _ = polynomialToLaurent (K := K) p * 1 := by rw [hinv]
      _ = polynomialToLaurent (K := K) p := mul_one _
  rw [hright]
  simpa [awayToLaurent, RingHom.comp_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    map_mul, map_pow, localizationAwayToLaurent_algebraMap,
    d, D, mul_comm] using hmapped

lemma polynomialToLaurent_support (p : S) :
    (polynomialToLaurent (K := K) p).coeff.support =
      Finset.image exponentToInt p.support := by
  change (AddMonoidAlgebra.mapDomain exponentToInt p).coeff.support = _
  rw [AddMonoidAlgebra.coeff_mapDomain,
    Finsupp.mapDomain_support_of_injective exponentToInt_injective,
    MvPolynomial.finsupp_support_eq_support]

lemma awayToLaurent_mk_mem_support_iff
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (r : ℕ) (p : S)
    (hp : p ∈ PS (r • (n + 1))) (a : LaurentExponent) :
    a ∈ (awayToLaurent (K := K) n f
        (HomogeneousLocalization.Away.mk PS
          (ProjectivePlaneNative.p2CechDenominator_mem (K := K) n f)
          r p hp)).coeff.support ↔
      ∃ b ∈ p.support, exponentToInt b - r • cechExponent n f = a := by
  rw [awayToLaurent_mk]
  rw [AddMonoidAlgebra.support_coeff_mul_single _ _ (by simp)]
  rw [polynomialToLaurent_support]
  simp only [Finset.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨c, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, by rw [addRightEmbedding_apply, sub_eq_add_neg]⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨exponentToInt b, ⟨b, hb, rfl⟩, ?_⟩
    rw [addRightEmbedding_apply, sub_eq_add_neg]

/-- Total exponent sum on a Laurent monomial.  Degree-zero homogeneous
fractions are supported on the kernel of this map. -/
def totalDegree (a : LaurentExponent) : ℤ := ∑ i, a i

/-- The coordinates at which a Laurent monomial has a negative exponent. -/
def negativeSupport (a : LaurentExponent) : Set (Fin 3) := {i | a i < 0}

lemma totalDegree_exponentToInt (b : Fin 3 →₀ ℕ) :
    totalDegree (exponentToInt b) = (∑ i, b i : ℕ) := by
  simp [totalDegree, exponentToInt_apply]

lemma finsupp_sum_eq_sum_support (b : Fin 3 →₀ ℕ) :
    ∑ i, b i = ∑ i ∈ b.support, b i := by
  classical
  symm
  refine Finset.sum_subset (Finset.subset_univ b.support) ?_
  intro i _ hi
  exact Finsupp.notMem_support_iff.mp hi

lemma totalDegree_eq_of_homogeneous_support
    {p : S} {d : ℕ} (hp : p ∈ PS d) {b : Fin 3 →₀ ℕ}
    (hb : b ∈ p.support) : totalDegree (exponentToInt b) = d := by
  rw [totalDegree_exponentToInt]
  norm_cast
  rw [finsupp_sum_eq_sum_support]
  exact (MvPolynomial.mem_homogeneousSubmodule d p).mp hp
    |>.degree_eq_sum_deg_support hb |>.symm

lemma totalDegree_add (a b : LaurentExponent) :
    totalDegree (a + b) = totalDegree a + totalDegree b := by
  simp [totalDegree, Finset.sum_add_distrib]

lemma totalDegree_neg (a : LaurentExponent) :
    totalDegree (-a) = - totalDegree a := by
  simp [totalDegree]

lemma totalDegree_nsmul (r : ℕ) (a : LaurentExponent) :
    totalDegree (r • a) = r • totalDegree a := by
  simp only [totalDegree, Finsupp.smul_apply, nsmul_eq_mul]
  rw [Finset.mul_sum]

lemma shifted_totalDegree_zero
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (r : ℕ)
    {p : S} (hp : p ∈ PS (r • (n + 1))) {b : Fin 3 →₀ ℕ}
    (hb : b ∈ p.support) :
    totalDegree (exponentToInt b - r • cechExponent n f) = 0 := by
  have hcech : totalDegree (cechExponent n f) = (n + 1 : ℕ) :=
    cechExponent_sum n f
  rw [sub_eq_add_neg, totalDegree_add, totalDegree_neg, totalDegree_nsmul,
    totalDegree_eq_of_homogeneous_support (K := K) hp hb, hcech]
  simp only [nsmul_eq_mul]
  push_cast
  ring

lemma shifted_negativeSupport_subset
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (r : ℕ)
    (b : Fin 3 →₀ ℕ) :
    negativeSupport (exponentToInt b - r • cechExponent n f) ⊆ Set.range f := by
  intro i hi
  change (exponentToInt b - r • cechExponent n f) i < 0 at hi
  simp only [Finsupp.sub_apply, exponentToInt_apply, Finsupp.smul_apply,
    nsmul_eq_mul] at hi
  have hpos : 0 < cechExponent n f i := by
    by_contra h
    have hzero : cechExponent n f i = 0 := by
      have hnonneg := cechExponent_nonneg n f i
      omega
    rw [hzero] at hi
    exact (not_lt_of_ge (Int.natCast_nonneg (b i))) hi
  exact (cechExponent_pos_iff n f i).mp hpos

/-- Every Laurent monomial occurring in a section on a standard Cech
intersection has total degree zero, and its negative coordinates are among
the coordinates inverted on that intersection. -/
theorem awayToLaurent_support_properties
    (n : ℕ) (f : Fin (n + 1) → Fin 3)
    (z : HomogeneousLocalization.Away PS
      (ProjectivePlaneNative.p2CechDenominator (K := K) n f)) :
    ∀ a ∈ (awayToLaurent (K := K) n f z).coeff.support,
      totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f := by
  obtain ⟨r, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective PS
    (ProjectivePlaneNative.p2CechDenominator_mem (K := K) n f) z
  intro a ha
  obtain ⟨b, hb, rfl⟩ :=
    (awayToLaurent_mk_mem_support_iff (K := K) n f r p hp a).mp ha
  exact ⟨shifted_totalDegree_zero (K := K) n f r hp hb,
    shifted_negativeSupport_subset n f r b⟩

/-- A uniform denominator exponent large enough to clear every negative
coordinate of a Laurent exponent. -/
def denominatorShift (a : LaurentExponent) : ℕ :=
  ∑ i, Int.natAbs (a i)

lemma natAbs_le_denominatorShift (a : LaurentExponent) (i : Fin 3) :
    Int.natAbs (a i) ≤ denominatorShift a := by
  classical
  unfold denominatorShift
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => Int.natAbs (a j))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma shiftedExponent_nonneg
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (a : LaurentExponent)
    (ha : negativeSupport a ⊆ Set.range f) (i : Fin 3) :
    0 ≤ a i + (denominatorShift a) • cechExponent n f i := by
  by_cases hi : i ∈ Set.range f
  · have hdelta : 0 < cechExponent n f i :=
      (cechExponent_pos_iff n f i).2 hi
    have habsNat := natAbs_le_denominatorShift a i
    have habsInt : (Int.natAbs (a i) : ℤ) ≤ denominatorShift a := by
      exact_mod_cast habsNat
    have hneg : -a i ≤ (Int.natAbs (a i) : ℤ) := by
      simpa using (Int.le_natAbs (a := -a i))
    simp only [nsmul_eq_mul]
    have hshift : (denominatorShift a : ℤ) ≤
        (denominatorShift a : ℤ) * cechExponent n f i := by
      exact le_mul_of_one_le_right (Int.natCast_nonneg _) hdelta
    omega
  · have hnotneg : ¬ a i < 0 := by
      intro h
      exact hi (ha h)
    have hdelta : cechExponent n f i = 0 := by
      have hnonneg := cechExponent_nonneg n f i
      have hnotpos : ¬ 0 < cechExponent n f i := by
        intro h
        exact hi ((cechExponent_pos_iff n f i).1 h)
      omega
    simp [hdelta, le_of_not_gt hnotneg]

/-- The ordinary monomial exponent obtained by clearing the negative
coordinates of a Laurent exponent on a Cech intersection. -/
def numeratorExponent
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (a : LaurentExponent) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i =>
    Int.toNat (a i + (denominatorShift a) • cechExponent n f i)

@[simp] lemma numeratorExponent_apply
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (a : LaurentExponent) (i : Fin 3) :
    numeratorExponent n f a i =
      Int.toNat (a i + (denominatorShift a) • cechExponent n f i) := by
  rfl

lemma exponentToInt_numeratorExponent_sub
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (a : LaurentExponent)
    (ha : negativeSupport a ⊆ Set.range f) :
    exponentToInt (numeratorExponent n f a) -
        (denominatorShift a) • cechExponent n f = a := by
  ext i
  simp only [Finsupp.sub_apply, exponentToInt_apply, numeratorExponent_apply,
    Finsupp.smul_apply]
  rw [Int.toNat_of_nonneg (shiftedExponent_nonneg n f a ha i)]
  omega

lemma numeratorExponent_degree
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (a : LaurentExponent)
    (hdegree : totalDegree a = 0)
    (hnegative : negativeSupport a ⊆ Set.range f) :
    (numeratorExponent n f a).degree = denominatorShift a • (n + 1) := by
  have hExp := exponentToInt_numeratorExponent_sub n f a hnegative
  have htd := congrArg totalDegree hExp
  have hcech : totalDegree (cechExponent n f) = (n + 1 : ℕ) :=
    cechExponent_sum n f
  rw [sub_eq_add_neg, totalDegree_add, totalDegree_neg, totalDegree_nsmul,
    totalDegree_exponentToInt, hcech, hdegree] at htd
  simp only [nsmul_eq_mul] at htd ⊢
  have hsum : (∑ i, numeratorExponent n f a i) = denominatorShift a * (n + 1) := by
    exact_mod_cast (sub_eq_zero.mp htd)
  rw [Finsupp.degree_apply, ← finsupp_sum_eq_sum_support]
  exact hsum

lemma numeratorMonomial_mem_homogeneous
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (a : LaurentExponent) (c : K)
    (hdegree : totalDegree a = 0)
    (hnegative : negativeSupport a ⊆ Set.range f) :
    MvPolynomial.monomial (numeratorExponent n f a) c ∈
      PS (denominatorShift a • (n + 1)) := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_monomial c
    (numeratorExponent_degree n f a hdegree hnegative)

lemma polynomialToLaurent_monomial (b : Fin 3 →₀ ℕ) (c : K) :
    polynomialToLaurent (K := K) (MvPolynomial.monomial b c) =
      AddMonoidAlgebra.single (exponentToInt b) c := by
  change AddMonoidAlgebra.mapDomain exponentToInt
    (AddMonoidAlgebra.single b c) = _
  rw [AddMonoidAlgebra.mapDomain_single]

lemma single_mem_range_awayToLaurent
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (a : LaurentExponent) (c : K)
    (hdegree : totalDegree a = 0)
    (hnegative : negativeSupport a ⊆ Set.range f) :
    ∃ z : HomogeneousLocalization.Away PS
        (ProjectivePlaneNative.p2CechDenominator (K := K) n f),
      awayToLaurent (K := K) n f z = AddMonoidAlgebra.single a c := by
  let r := denominatorShift a
  let b := numeratorExponent n f a
  have hp : MvPolynomial.monomial b c ∈ PS (r • (n + 1)) := by
    exact numeratorMonomial_mem_homogeneous (K := K) n f a c hdegree hnegative
  refine ⟨HomogeneousLocalization.Away.mk PS
      (ProjectivePlaneNative.p2CechDenominator_mem (K := K) n f)
      r (MvPolynomial.monomial b c) hp, ?_⟩
  rw [awayToLaurent_mk, polynomialToLaurent_monomial,
    AddMonoidAlgebra.single_mul_single, mul_one]
  congr
  simpa [b, r, sub_eq_add_neg] using
    (exponentToInt_numeratorExponent_sub n f a hnegative)

/-- Conversely, every finite Laurent sum with total degree zero and negative
support confined to the inverted coordinates comes from the homogeneous
localization on that Cech intersection. -/
theorem exists_awayToLaurent_eq_of_support
    (n : ℕ) (f : Fin (n + 1) → Fin 3) (g : LaurentPolynomial K)
    (hg : ∀ a ∈ g.coeff.support,
      totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f) :
    ∃ z : HomogeneousLocalization.Away PS
        (ProjectivePlaneNative.p2CechDenominator (K := K) n f),
      awayToLaurent (K := K) n f z = g := by
  classical
  let preimage : LaurentExponent →
      HomogeneousLocalization.Away PS
        (ProjectivePlaneNative.p2CechDenominator (K := K) n f) := fun a =>
    if ha : a ∈ g.coeff.support then
      Classical.choose (single_mem_range_awayToLaurent (K := K) n f a (g.coeff a)
        (hg a ha).1 (hg a ha).2)
    else 0
  have hpreimage : ∀ a ∈ g.coeff.support,
      awayToLaurent (K := K) n f (preimage a) =
        AddMonoidAlgebra.single a (g.coeff a) := by
    intro a ha
    simp only [preimage, dif_pos ha]
    exact Classical.choose_spec
      (single_mem_range_awayToLaurent (K := K) n f a (g.coeff a)
        (hg a ha).1 (hg a ha).2)
  refine ⟨∑ a ∈ g.coeff.support, preimage a, ?_⟩
  rw [map_sum]
  calc
    ∑ a ∈ g.coeff.support, awayToLaurent (K := K) n f (preimage a) =
        ∑ a ∈ g.coeff.support, AddMonoidAlgebra.single a (g.coeff a) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hpreimage a ha
    _ = g := by
      simpa [Finsupp.sum] using (AddMonoidAlgebra.sum_coeff_single g)

/-- Delete the `i`th entry from an ordered Cech tuple. -/
def deleteTuple {n : ℕ} (i : Fin (n + 2))
    (f : Fin (n + 2) → Fin 3) : Fin (n + 1) → Fin 3 :=
  fun j => f (i.succAbove j)

lemma p2CechDenominator_succ_eq_deleteTuple_mul
    (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3) :
    ProjectivePlaneNative.p2CechDenominator (K := K) (n + 1) f =
      ProjectivePlaneNative.p2CechDenominator (K := K) n (deleteTuple i f) *
        MvPolynomial.X (R := K) (f i) := by
  simp only [ProjectivePlaneNative.p2CechDenominator]
  rw [Fin.prod_univ_succAbove
    (fun j : Fin (n + 2) => MvPolynomial.X (R := K) (f j)) i]
  simp [deleteTuple, mul_comm]

lemma cechExponent_succ_eq_deleteTuple_add
    (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3) :
    cechExponent (n + 1) f =
      cechExponent n (deleteTuple i f) + Finsupp.single (f i) 1 := by
  simp only [cechExponent]
  rw [Fin.sum_univ_succAbove
    (fun j : Fin (n + 2) => (Finsupp.single (f j) (1 : ℤ) : LaurentExponent)) i]
  simp [deleteTuple, add_comm]

lemma coordinate_mem_degree_one (j : Fin 3) :
    MvPolynomial.X (R := K) j ∈ PS 1 := by
  exact MvPolynomial.isHomogeneous_X K j

/-- The homogeneous-localization restriction map associated to deleting one
entry of an ordered Cech tuple. -/
def awayFaceMap
    (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3) :
    HomogeneousLocalization.Away PS
        (ProjectivePlaneNative.p2CechDenominator (K := K) n (deleteTuple i f)) →+*
      HomogeneousLocalization.Away PS
        (ProjectivePlaneNative.p2CechDenominator (K := K) (n + 1) f) :=
  HomogeneousLocalization.awayMap PS (coordinate_mem_degree_one (K := K) (f i))
    (p2CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f)

/-- All face restrictions become literal inclusions in the common Laurent
polynomial model. -/
lemma awayToLaurent_awayFaceMap
    (n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3)
    (z : HomogeneousLocalization.Away PS
      (ProjectivePlaneNative.p2CechDenominator (K := K) n (deleteTuple i f))) :
    awayToLaurent (K := K) (n + 1) f (awayFaceMap (K := K) n i f z) =
      awayToLaurent (K := K) n (deleteTuple i f) z := by
  obtain ⟨r, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective PS
    (ProjectivePlaneNative.p2CechDenominator_mem (K := K) n (deleteTuple i f)) z
  rw [awayFaceMap, HomogeneousLocalization.awayMap_mk]
  rw [awayToLaurent_mk, awayToLaurent_mk]
  rw [map_mul, map_pow, polynomialToLaurent_X]
  rw [AddMonoidAlgebra.single_pow]
  rw [cechExponent_succ_eq_deleteTuple_add n i f]
  simp only [nsmul_add]
  rw [mul_assoc, AddMonoidAlgebra.single_mul_single]
  simp only [one_pow, one_mul]
  congr 1
  abel_nf

end PlaneLaurentLocalization
end PfaffianDescent

import PfaffianDescent.VoisinLaurentCechExact

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped AddMonoidAlgebra BigOperators
universe u
namespace PfaffianDescent.AwayCechExact

open LaurentLocalization LaurentCechCore LaurentCechExact

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

abbrev AwayCochain (q : ℕ) :=
  (f : Fin (q + 1) → Fin 4) →
    HomogeneousLocalization.Away PS
      (ProjectiveNegativeTwist.p3CechDenominator (K := K) q f)

def toLaurent {q : ℕ} (x : AwayCochain K q) :
    (Fin (q + 1) → Fin 4) → LaurentLocalization.LaurentPolynomial K :=
  fun f => awayToLaurent (K := K) q f (x f)

@[simp] lemma deleteTuple_two_zero (f : Fin 2 → Fin 4) :
    deleteTuple (0 : Fin 2) f = ![f 1] := by
  funext j
  fin_cases j
  rfl

@[simp] lemma deleteTuple_two_one (f : Fin 2 → Fin 4) :
    deleteTuple (1 : Fin 2) f = ![f 0] := by
  funext j
  fin_cases j
  rfl

@[simp] lemma deleteTuple_three_zero (f : Fin 3 → Fin 4) :
    deleteTuple (0 : Fin 3) f = ![f 1, f 2] := by
  funext j
  fin_cases j <;> rfl

@[simp] lemma deleteTuple_three_one (f : Fin 3 → Fin 4) :
    deleteTuple (1 : Fin 3) f = ![f 0, f 2] := by
  funext j
  fin_cases j <;> rfl

@[simp] lemma deleteTuple_three_two (f : Fin 3 → Fin 4) :
    deleteTuple (2 : Fin 3) f = ![f 0, f 1] := by
  funext j
  fin_cases j <;> rfl

@[simp] lemma deleteTuple_four_zero (f : Fin 4 → Fin 4) :
    deleteTuple (0 : Fin 4) f = ![f 1, f 2, f 3] := by
  funext j
  fin_cases j <;> rfl

@[simp] lemma deleteTuple_four_one (f : Fin 4 → Fin 4) :
    deleteTuple (1 : Fin 4) f = ![f 0, f 2, f 3] := by
  funext j
  fin_cases j <;> rfl

@[simp] lemma deleteTuple_four_two (f : Fin 4 → Fin 4) :
    deleteTuple (2 : Fin 4) f = ![f 0, f 1, f 3] := by
  funext j
  fin_cases j <;> rfl

@[simp] lemma deleteTuple_four_three (f : Fin 4 → Fin 4) :
    deleteTuple (3 : Fin 4) f = ![f 0, f 1, f 2] := by
  funext j
  fin_cases j <;> rfl

/-- Algebraic Cech differential on degree-zero homogeneous localizations. -/
def awayD0 (x : AwayCochain K 0) : AwayCochain K 1 := fun f =>
  awayFaceMap (K := K) 0 0 f (x (deleteTuple 0 f)) -
    awayFaceMap (K := K) 0 1 f (x (deleteTuple 1 f))

/-- Algebraic Cech differential in degree one. -/
def awayD1 (y : AwayCochain K 1) : AwayCochain K 2 := fun f =>
  awayFaceMap (K := K) 1 0 f (y (deleteTuple 0 f)) -
    awayFaceMap (K := K) 1 1 f (y (deleteTuple 1 f)) +
    awayFaceMap (K := K) 1 2 f (y (deleteTuple 2 f))

/-- Algebraic Cech differential in degree two. -/
def awayD2 (z : AwayCochain K 2) : AwayCochain K 3 := fun f =>
  awayFaceMap (K := K) 2 0 f (z (deleteTuple 0 f)) -
    awayFaceMap (K := K) 2 1 f (z (deleteTuple 1 f)) +
    awayFaceMap (K := K) 2 2 f (z (deleteTuple 2 f)) -
    awayFaceMap (K := K) 2 3 f (z (deleteTuple 3 f))

lemma toLaurent_awayD0 (x : AwayCochain K 0) :
    toLaurent K (awayD0 K x) = tupleD0 (toLaurent K x) := by
  funext f
  simp only [toLaurent, awayD0, map_sub, awayToLaurent_awayFaceMap,
    tupleD0]
  rw [deleteTuple_two_zero f, deleteTuple_two_one f]

lemma toLaurent_awayD1 (y : AwayCochain K 1) :
    toLaurent K (awayD1 K y) = tupleD1 (toLaurent K y) := by
  funext f
  simp only [toLaurent, awayD1, map_add, map_sub, awayToLaurent_awayFaceMap,
    tupleD1]
  rw [deleteTuple_three_zero f, deleteTuple_three_one f, deleteTuple_three_two f]

lemma toLaurent_awayD2 (z : AwayCochain K 2) :
    toLaurent K (awayD2 K z) = tupleD2 (toLaurent K z) := by
  funext f
  simp only [toLaurent, awayD2, map_add, map_sub, awayToLaurent_awayFaceMap,
    tupleD2]
  rw [deleteTuple_four_zero f, deleteTuple_four_one f,
    deleteTuple_four_two f, deleteTuple_four_three f]

/-- Exactness in degree one of the ordered four-chart Cech complex written in
homogeneous degree-zero localizations. -/
theorem away_exact_one
    (y : AwayCochain K 1) (hdy : ∀ f, awayD1 K y f = 0) :
    ∃ x : AwayCochain K 0, ∀ f, awayD0 K x f = y f := by
  have hy : ∀ f (a : LaurentLocalization.LaurentExponent),
      a ∈ ((toLaurent K y) f).coeff.support →
        totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f := by
    intro f a ha
    exact awayToLaurent_support_properties (K := K) 1 f (y f) a ha
  have hdyL : ∀ f, tupleD1 (toLaurent K y) f = 0 := by
    intro f
    rw [← congrFun (toLaurent_awayD1 K y) f]
    change awayToLaurent (K := K) 2 f (awayD1 K y f) = 0
    rw [hdy f, map_zero]
  obtain ⟨xL, hxL, hdiff⟩ := laurent_tuple_exact_one K (toLaurent K y) hy hdyL
  have hlift (f : Fin 1 → Fin 4) :
      ∃ z : HomogeneousLocalization.Away PS
          (ProjectiveNegativeTwist.p3CechDenominator (K := K) 0 f),
        awayToLaurent (K := K) 0 f z = xL f :=
    exists_awayToLaurent_eq_of_support (K := K) 0 f (xL f) (hxL f)
  let x : AwayCochain K 0 := fun f => Classical.choose (hlift f)
  have hx (f : Fin 1 → Fin 4) :
      awayToLaurent (K := K) 0 f (x f) = xL f :=
    Classical.choose_spec (hlift f)
  refine ⟨x, fun f => ?_⟩
  apply awayToLaurent_injective (K := K) 1 f
  calc
    awayToLaurent (K := K) 1 f (awayD0 K x f) =
        tupleD0 (toLaurent K x) f := congrFun (toLaurent_awayD0 K x) f
    _ = tupleD0 xL f := by
      simp only [tupleD0, toLaurent]
      rw [hx ![f 1], hx ![f 0]]
    _ = (toLaurent K y) f := hdiff f
    _ = awayToLaurent (K := K) 1 f (y f) := rfl

/-- Exactness in degree two of the ordered four-chart Cech complex written in
homogeneous degree-zero localizations. -/
theorem away_exact_two
    (z : AwayCochain K 2) (hdz : ∀ f, awayD2 K z f = 0) :
    ∃ y : AwayCochain K 1, ∀ f, awayD1 K y f = z f := by
  have hz : ∀ f (a : LaurentLocalization.LaurentExponent),
      a ∈ ((toLaurent K z) f).coeff.support →
        totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f := by
    intro f a ha
    exact awayToLaurent_support_properties (K := K) 2 f (z f) a ha
  have hdzL : ∀ f, tupleD2 (toLaurent K z) f = 0 := by
    intro f
    rw [← congrFun (toLaurent_awayD2 K z) f]
    change awayToLaurent (K := K) 3 f (awayD2 K z f) = 0
    rw [hdz f, map_zero]
  obtain ⟨yL, hyL, hdiff⟩ := laurent_tuple_exact_two K (toLaurent K z) hz hdzL
  have hlift (f : Fin 2 → Fin 4) :
      ∃ y : HomogeneousLocalization.Away PS
          (ProjectiveNegativeTwist.p3CechDenominator (K := K) 1 f),
        awayToLaurent (K := K) 1 f y = yL f :=
    exists_awayToLaurent_eq_of_support (K := K) 1 f (yL f) (hyL f)
  let y : AwayCochain K 1 := fun f => Classical.choose (hlift f)
  have hy (f : Fin 2 → Fin 4) :
      awayToLaurent (K := K) 1 f (y f) = yL f :=
    Classical.choose_spec (hlift f)
  refine ⟨y, fun f => ?_⟩
  apply awayToLaurent_injective (K := K) 2 f
  calc
    awayToLaurent (K := K) 2 f (awayD1 K y f) =
        tupleD1 (toLaurent K y) f := congrFun (toLaurent_awayD1 K y) f
    _ = tupleD1 yL f := by
      simp only [tupleD1, toLaurent]
      rw [hy ![f 1, f 2], hy ![f 0, f 2], hy ![f 0, f 1]]
    _ = (toLaurent K z) f := hdiff f
    _ = awayToLaurent (K := K) 2 f (z f) := rfl

end PfaffianDescent.AwayCechExact

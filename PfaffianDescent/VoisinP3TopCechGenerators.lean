import PfaffianDescent.VoisinP3TopCechRawResidue
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Explicit generators for top projective Cech residues

The determinant of the vertex-incidence matrix gives the orientation
cochain of the four-vertex simplex.  Multiplying it by a full-negative
Laurent monomial produces a top Cech cocycle whose corresponding residue is
one.  This supplies the existence half of the explicit `P³` Serre pairing.
-/

noncomputable section

open scoped AddMonoidAlgebra BigOperators

namespace PfaffianDescent

namespace LaurentCechCore

/-- Orientation number of an ordered quadruple of the four standard
vertices.  It is the determinant of its `0`-`1` incidence matrix. -/
def tupleOrientation (f : Fin 4 → Vertex) : ℤ :=
  Matrix.det fun i j => if f j = i then 1 else 0

@[simp]
lemma tupleOrientation_id : tupleOrientation id = 1 := by
  have hmatrix : (fun i j : Fin 4 => if id j = i then (1 : ℤ) else 0) =
      (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, eq_comm]
  rw [tupleOrientation, hmatrix]
  exact Matrix.det_one

lemma tupleOrientation_eq_zero_of_not_surjective
    (f : Fin 4 → Vertex) (hf : ¬ Function.Surjective f) :
    tupleOrientation f = 0 := by
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    exact hf ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, rfl⟩).2
  rw [Function.not_injective_iff] at hnotinj
  obtain ⟨i, j, hfij, hij⟩ := hnotinj
  unfold tupleOrientation
  apply Matrix.det_zero_of_column_eq hij
  intro k
  rw [hfij]

/-- The five-term boundary expression for the orientation cochain. -/
def tupleOrientationBoundary (a b c d e : Vertex) : ℤ :=
  tupleOrientation ![b, c, d, e] - tupleOrientation ![a, c, d, e] +
    tupleOrientation ![a, b, d, e] - tupleOrientation ![a, b, c, e] +
      tupleOrientation ![a, b, c, d]

private lemma tupleOrientationBoundary_zero_first_zero
    (b c d e : Vertex) : tupleOrientationBoundary 0 b c d e = 0 := by
  decide +revert

private lemma tupleOrientationBoundary_zero_first_one
    (b c d e : Vertex) : tupleOrientationBoundary 1 b c d e = 0 := by
  decide +revert

private lemma tupleOrientationBoundary_zero_first_two
    (b c d e : Vertex) : tupleOrientationBoundary 2 b c d e = 0 := by
  decide +revert

private lemma tupleOrientationBoundary_zero_first_three
    (b c d e : Vertex) : tupleOrientationBoundary 3 b c d e = 0 := by
  decide +revert

/-- The orientation cochain is a degree-three Cech cocycle.  This finite
identity is the boundary-of-the-oriented-simplex cancellation. -/
lemma tupleOrientation_cocycle (f : Fin 5 → Vertex) :
    tupleOrientation ![f 1, f 2, f 3, f 4] -
      tupleOrientation ![f 0, f 2, f 3, f 4] +
      tupleOrientation ![f 0, f 1, f 3, f 4] -
      tupleOrientation ![f 0, f 1, f 2, f 4] +
      tupleOrientation ![f 0, f 1, f 2, f 3] = 0 := by
  change tupleOrientationBoundary (f 0) (f 1) (f 2) (f 3) (f 4) = 0
  generalize _ha : f 0 = a
  fin_cases a
  · exact tupleOrientationBoundary_zero_first_zero
      (f 1) (f 2) (f 3) (f 4)
  · exact tupleOrientationBoundary_zero_first_one
      (f 1) (f 2) (f 3) (f 4)
  · exact tupleOrientationBoundary_zero_first_two
      (f 1) (f 2) (f 3) (f 4)
  · exact tupleOrientationBoundary_zero_first_three
      (f 1) (f 2) (f 3) (f 4)

/-- Scalar-valued orientation cocycle. -/
def scalarOrientationCochain {A : Type*} [AddCommGroup A]
    (c : A) : (Fin 4 → Vertex) → A :=
  fun f => tupleOrientation f • c

lemma scalarOrientationCochain_supported {A : Type*} [AddCommGroup A]
    (c : A) :
    TupleSupported Set.univ (scalarOrientationCochain c) := by
  intro f hf
  have hnotsurj : ¬ Function.Surjective f := by
    intro hsurj
    apply hf
    rw [Set.range_eq_univ.mpr hsurj]
  simp [scalarOrientationCochain,
    tupleOrientation_eq_zero_of_not_surjective f hnotsurj]

lemma scalarOrientationCochain_tupleD3 {A : Type*} [AddCommGroup A]
    (c : A) (f : Fin 5 → Vertex) :
    tupleD3 (scalarOrientationCochain c) f = 0 := by
  have h := congrArg (fun z : ℤ => z • c) (tupleOrientation_cocycle f)
  simpa [tupleD3, scalarOrientationCochain, sub_eq_add_neg,
    add_zsmul, neg_zsmul] using h

@[simp]
lemma scalarOrientationCochain_id {A : Type*} [AddCommGroup A]
    (c : A) : scalarOrientationCochain c id = c := by
  simp [scalarOrientationCochain]

end LaurentCechCore

namespace LaurentCechExact

open LaurentLocalization LaurentCechCore

universe u

variable (K : Type u) [Field K]

/-- Laurent top cocycle representing the residue coordinate dual to the
quadratic monomial `b`. -/
def p3SerreLaurentGenerator (b : Fin 4 →₀ ℕ) :
    (Fin 4 → Fin 4) → LaurentPolynomial K :=
  fun f => AddMonoidAlgebra.single (p3SerreDualExponent b)
    (tupleOrientation f • (1 : K))

lemma p3SerreLaurentGenerator_support
    (b : Fin 4 →₀ ℕ) (hb : b.degree = 2)
    (f : Fin 4 → Fin 4) (a : LaurentExponent)
    (ha : a ∈ (p3SerreLaurentGenerator K b f).coeff.support) :
    totalDegree a = -6 ∧ negativeSupport a ⊆ Set.range f := by
  have hcoeff :
      (p3SerreLaurentGenerator K b f).coeff a ≠ 0 :=
    Finsupp.mem_support_iff.mp ha
  have haeq : a = p3SerreDualExponent b := by
    by_contra hne
    apply hcoeff
    simp [p3SerreLaurentGenerator, AddMonoidAlgebra.coeff_single, hne]
  subst a
  refine ⟨p3SerreDualExponent_totalDegree_of_degree_two b hb, ?_⟩
  rw [p3SerreDualExponent_negativeSupport]
  rw [Set.range_eq_univ.mpr]
  intro y
  by_contra hy
  have hnotsurj : ¬ Function.Surjective f := by
    intro hsurj
    exact hy (hsurj y)
  apply hcoeff
  simp [p3SerreLaurentGenerator,
    tupleOrientation_eq_zero_of_not_surjective f hnotsurj]

lemma p3SerreLaurentGenerator_cocycle
    (b : Fin 4 →₀ ℕ) (f : Fin 5 → Fin 4) :
    tupleD3 (p3SerreLaurentGenerator K b) f = 0 := by
  ext a
  by_cases ha : a = p3SerreDualExponent b
  · subst a
    have h := congrArg (Int.castRingHom K) (tupleOrientation_cocycle f)
    simpa [p3SerreLaurentGenerator, tupleD3,
      AddMonoidAlgebra.coeff_single] using h
  · simp [p3SerreLaurentGenerator, tupleD3,
      AddMonoidAlgebra.coeff_single, ha]

@[simp]
lemma p3SerreResidueCoefficient_generator_self
    (b : Fin 4 →₀ ℕ) :
    p3SerreResidueCoefficient K b (p3SerreLaurentGenerator K b) = 1 := by
  change (AddMonoidAlgebra.single (p3SerreDualExponent b)
    (tupleOrientation id • (1 : K))).coeff (p3SerreDualExponent b) = 1
  simp

lemma p3SerreResidueCoefficient_generator
    (b c : Fin 4 →₀ ℕ) :
    p3SerreResidueCoefficient K c (p3SerreLaurentGenerator K b) =
      if c = b then 1 else 0 := by
  by_cases hcb : c = b
  · subst c
    rw [if_pos rfl]
    exact p3SerreResidueCoefficient_generator_self K b
  · have hexp : p3SerreDualExponent c ≠ p3SerreDualExponent b := by
      exact fun h => hcb (p3SerreDualExponent_injective h)
    simp [p3SerreLaurentGenerator, AddMonoidAlgebra.coeff_single,
      hcb, hexp]

end LaurentCechExact

namespace ProjectiveNegativeTwist

open LaurentLocalization LaurentCechCore LaurentCechExact

universe u

variable (K : Type u) [Field K]

/-- A raw degree-three Cech cochain lifting the Laurent orientation generator
for a quadratic monomial. -/
noncomputable def p3NegativeSixRawGenerator
    (b : {b : Fin 4 →₀ ℕ // b.degree = 2}) :
    (p3NegativeTwistCechComplex (K := K) 6).X 3 :=
  Classical.choose
    (exists_p3NegativeTwistCechTermToLaurent_eq_of_support K 6 3
      (p3SerreLaurentGenerator K b)
      (p3SerreLaurentGenerator_support K b b.property))

lemma p3NegativeSixRawGenerator_toLaurent
    (b : {b : Fin 4 →₀ ℕ // b.degree = 2}) :
    p3NegativeTwistCechTermToLaurent K 6 3
        (p3NegativeSixRawGenerator K b) =
      p3SerreLaurentGenerator K b :=
  Classical.choose_spec
    (exists_p3NegativeTwistCechTermToLaurent_eq_of_support K 6 3
      (p3SerreLaurentGenerator K b)
      (p3SerreLaurentGenerator_support K b b.property))

/-- The lifted orientation generator is an actual raw top Cech cocycle. -/
lemma p3NegativeSixRawGenerator_cocycle
    (b : {b : Fin 4 →₀ ℕ // b.degree = 2}) :
    (p3NegativeTwistCechComplex (K := K) 6).d 3 4
      (p3NegativeSixRawGenerator K b) = 0 := by
  apply p3NegativeTwistCechTermToLaurent_injective K 6 4
  rw [p3NegativeTwistCechTermToLaurent_d_three K 6,
    p3NegativeSixRawGenerator_toLaurent K b]
  funext f
  rw [p3SerreLaurentGenerator_cocycle K b f]
  simp

/-- The raw generator has the Kronecker-delta residue coordinates. -/
lemma p3NegativeSixRawResidue_generator
    (b : {b : Fin 4 →₀ ℕ // b.degree = 2}) (c : Fin 4 →₀ ℕ) :
    p3NegativeSixRawResidue K c (p3NegativeSixRawGenerator K b) =
      if c = b then 1 else 0 := by
  rw [p3NegativeSixRawResidue_apply,
    p3NegativeSixRawGenerator_toLaurent]
  exact p3SerreResidueCoefficient_generator K b c

/-- Every quadratic monomial residue coordinate is represented by a raw top
cocycle and is normalized to one on its own coordinate. -/
theorem exists_p3NegativeSixRawCocycle_residue_one
    (b : Fin 4 →₀ ℕ) (hb : b.degree = 2) :
    ∃ w : (p3NegativeTwistCechComplex (K := K) 6).X 3,
      (p3NegativeTwistCechComplex (K := K) 6).d 3 4 w = 0 ∧
      p3NegativeSixRawResidue K b w = 1 := by
  let b' : {c : Fin 4 →₀ ℕ // c.degree = 2} := ⟨b, hb⟩
  refine ⟨p3NegativeSixRawGenerator K b',
    p3NegativeSixRawGenerator_cocycle K b', ?_⟩
  simpa [b'] using p3NegativeSixRawResidue_generator K b' b

end ProjectiveNegativeTwist

end PfaffianDescent

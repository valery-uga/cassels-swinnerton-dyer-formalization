import PfaffianDescent.GrassmannianOverlapDeterminant
import Mathlib.Algebra.MvPolynomial.Eval

namespace PfaffianDescent
open Matrix
section
variable (R : Type*) [CommRing R] {m n : ℕ}

/-- Ambient coordinate permutations, expressed in two coordinate blocks. -/
def graphCoordinatePermutation (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    ((Fin m → R) × (Fin n → R)) ≃ₗ[R] ((Fin m → R) × (Fin n → R)) :=
  (LinearEquiv.sumArrowLequivProdArrow _ _ R R).symm.trans
    ((LinearEquiv.funCongrLeft R R σ).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ R R))

lemma graphCoordinatePermutation_fst (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (x : (Fin m → R) × (Fin n → R)) (i : Fin m) :
    (graphCoordinatePermutation R σ x).1 i = Sum.elim x.1 x.2 (σ (Sum.inl i)) := rfl

lemma graphCoordinatePermutation_snd (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (x : (Fin m → R) × (Fin n → R)) (i : Fin n) :
    (graphCoordinatePermutation R σ x).2 i = Sum.elim x.1 x.2 (σ (Sum.inr i)) := rfl

end

section
variable {R : Type*} [CommRing R] {m n : ℕ}

/-- The graph's full column matrix has an identity block above its parameter matrix. -/
def graphColumnEntry (T : Matrix (Fin n) (Fin m) R) (i : Fin m ⊕ Fin n) (j : Fin m) : R :=
  Sum.elim (fun k => if k = j then 1 else 0) (fun k => T k j) i

/-- The minor selected by the first block of a coordinate permutation. -/
def graphOverlapMatrix (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    Matrix (Fin m) (Fin m) R :=
  fun i j => graphColumnEntry T (σ (Sum.inl i)) j

lemma graphOverlapMatrix_toLin (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) :
    Matrix.toLin' (graphOverlapMatrix σ T) =
      graphTransitionFirst (graphCoordinatePermutation R σ) (Matrix.toLin' T) := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_toLin']
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change graphColumnEntry T (σ (Sum.inl i)) j =
    Sum.elim (Pi.single j 1) (T *ᵥ Pi.single j 1) (σ (Sum.inl i))
  cases h : σ (Sum.inl i) with
  | inl k => simp [graphColumnEntry, Pi.single_apply, eq_comm]
  | inr k => simp [graphColumnEntry]

/-- The open-overlap determinant is the corresponding maximal graph minor. -/
lemma graphOverlapMatrix_det (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) :
    (graphOverlapMatrix σ T).det =
      graphOverlapDeterminant (graphCoordinatePermutation R σ) (Matrix.toLin' T) := by
  rw [graphOverlapDeterminant, ← graphOverlapMatrix_toLin, LinearMap.det_toLin']

lemma graphColumnEntry_map {S : Type*} [CommRing S] (φ : R →+* S)
    (T : Matrix (Fin n) (Fin m) R) (i : Fin m ⊕ Fin n) (j : Fin m) :
    φ (graphColumnEntry T i j) = graphColumnEntry (T.map φ) i j := by
  rcases i with i | i
  · by_cases h : i = j <;> simp [graphColumnEntry, h]
  · rfl

lemma graphOverlapMatrix_map {S : Type*} [CommRing S] (φ : R →+* S)
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    (graphOverlapMatrix σ T).map φ = graphOverlapMatrix σ (T.map φ) := by
  ext i j
  exact graphColumnEntry_map φ T _ _

end

section
variable (K : Type*) [CommRing K] {m n : ℕ}

/-- The coordinate algebra of a Grassmannian graph chart. -/
abbrev GrassmannianChartRing (m n : ℕ) := MvPolynomial (Fin n × Fin m) K

/-- Universal polynomial defining an overlap of two graph charts. -/
noncomputable def grassmannianOverlapPolynomial (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    GrassmannianChartRing K m n :=
  (graphOverlapMatrix σ (fun i j => MvPolynomial.X (i, j))).det

lemma grassmannianOverlapPolynomial_eval {A : Type*} [CommRing A] [Algebra K A]
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) A) :
    MvPolynomial.aeval (fun ij : Fin n × Fin m => T ij.1 ij.2) (grassmannianOverlapPolynomial K σ) =
      graphOverlapDeterminant (graphCoordinatePermutation A σ) (Matrix.toLin' T) := by
  let φ : GrassmannianChartRing K m n →+* A :=
    (MvPolynomial.aeval (fun ij : Fin n × Fin m => T ij.1 ij.2)).toRingHom
  let U : Matrix (Fin n) (Fin m) (GrassmannianChartRing K m n) :=
    Matrix.of (fun i j => MvPolynomial.X (i, j))
  change φ (graphOverlapMatrix σ U).det = _
  rw [RingHom.map_det]
  change ((graphOverlapMatrix σ U).map φ).det = _
  rw [graphOverlapMatrix_map]
  have hX : U.map φ = T := by
    ext i j
    exact MvPolynomial.aeval_X _ _
  rw [hX, graphOverlapMatrix_det]

/-- Arbitrary algebra-valued points lie in the overlap exactly when the
universal overlap polynomial is a unit at that point. -/
theorem grassmannianOverlapPolynomial_chart_iff {A : Type*} [CommRing A] [Algebra K A]
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) A) :
    IsUnit (MvPolynomial.aeval (fun ij : Fin n × Fin m => T ij.1 ij.2) (grassmannianOverlapPolynomial K σ)) ↔
      Function.Bijective (graphChartQuotientMap
        ((Matrix.toLin' T).graph.map (graphCoordinatePermutation A σ).toLinearMap)) := by
  rw [grassmannianOverlapPolynomial_eval]
  exact grassmannian_overlap_determinant_iff _ _

end
end PfaffianDescent

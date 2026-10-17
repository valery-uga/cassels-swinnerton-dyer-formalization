import PfaffianDescent.GoodMatrixGraphNaturality
import PfaffianDescent.GoodFiberAlgebraEquiv

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]

/-- All entries of the restrictions of the three forms to the universal graph. -/
def goodGraphRelation (T : Matrix (Fin 3) (Fin 3) R) (k : Fin 3 × Fin 3 × Fin 3) : R :=
  ![T k.2.1 k.2.2 - T k.2.2 k.2.1,
    goodBlockEigenvalue R k.2.1 * T k.2.1 k.2.2 -
      goodBlockEigenvalue R k.2.2 * T k.2.2 k.2.1,
    goodGraphThirdEntry R T k.2.1 k.2.2] k.1

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodGraphRelation_map (φ : R →+* S) (T : Matrix (Fin 3) (Fin 3) R)
    (k : Fin 3 × Fin 3 × Fin 3) :
    goodGraphRelation S (T.map φ) k = φ (goodGraphRelation R T k) := by
  rcases k with ⟨b, i, j⟩
  fin_cases b
  · simp [goodGraphRelation, map_sub]
  · simp [goodGraphRelation, map_sub, map_mul, goodBlockEigenvalue_map]
  · exact goodGraphThirdEntry_map φ T i j

end
section
variable (K : Type*) [CommRing K]

abbrev GoodGraphFiberPolynomial := MvPolynomial (Fin 3 × Fin 3) K

noncomputable def goodGraphFiberUniversalMatrix : Matrix (Fin 3) (Fin 3) (GoodGraphFiberPolynomial K) :=
  fun i j => MvPolynomial.X (i, j)

noncomputable def goodGraphFiberRelations (k : Fin 3 × Fin 3 × Fin 3) : GoodGraphFiberPolynomial K :=
  goodGraphRelation _ (goodGraphFiberUniversalMatrix K) k

noncomputable def goodGraphFiberIdeal : Ideal (GoodGraphFiberPolynomial K) :=
  Ideal.span (Set.range (goodGraphFiberRelations K))

/-- The complete graph-chart quotient by all three restrictions, before eliminating variables. -/
abbrev GoodGraphFiberAlgebra := GoodGraphFiberPolynomial K ⧸ goodGraphFiberIdeal K

noncomputable def goodGraphFiberX (i j : Fin 3) : GoodGraphFiberAlgebra K :=
  Ideal.Quotient.mkₐ K (goodGraphFiberIdeal K) (MvPolynomial.X (i, j))

lemma goodGraphFiberRelations_eval {A : Type*} [CommRing A] [Algebra K A]
    (T : Matrix (Fin 3) (Fin 3) A) (k : Fin 3 × Fin 3 × Fin 3) :
    MvPolynomial.aeval (R := K) (fun ij => T ij.1 ij.2) (goodGraphFiberRelations K k) =
      goodGraphRelation A T k := by
  let φ : GoodGraphFiberPolynomial K →+* A :=
    (MvPolynomial.aeval (R := K) (fun ij : Fin 3 × Fin 3 => T ij.1 ij.2)).toRingHom
  have he : (goodGraphFiberUniversalMatrix K).map φ = T := by
    funext i j
    exact MvPolynomial.aeval_X _ _
  have hmap := goodGraphRelation_map φ (goodGraphFiberUniversalMatrix K) k
  rw [he] at hmap
  exact hmap.symm

lemma goodGraphFiberX_relation (k : Fin 3 × Fin 3 × Fin 3) :
    goodGraphRelation (GoodGraphFiberAlgebra K) (goodGraphFiberX K) k = 0 := by
  have hz : Ideal.Quotient.mkₐ K (goodGraphFiberIdeal K) (goodGraphFiberRelations K k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, rfl⟩)
  exact (goodGraphRelation_map (Ideal.Quotient.mkₐ K (goodGraphFiberIdeal K)).toRingHom
    (goodGraphFiberUniversalMatrix K) k).trans hz

/-- Evaluation of a graph matrix satisfying the actual restriction equations. -/
noncomputable def goodGraphFiberLift {A : Type*} [CommRing A] [Algebra K A]
    (T : Matrix (Fin 3) (Fin 3) A) (hT : ∀ k, goodGraphRelation A T k = 0) :
    GoodGraphFiberAlgebra K →ₐ[K] A :=
  Ideal.Quotient.liftₐ (goodGraphFiberIdeal K)
    (MvPolynomial.aeval (R := K) (fun ij => T ij.1 ij.2)) (by
      have hle : goodGraphFiberIdeal K ≤ RingHom.ker
          (MvPolynomial.aeval (R := K) (fun ij => T ij.1 ij.2)).toRingHom := by
        apply Ideal.span_le.mpr
        rintro _ ⟨k, rfl⟩
        exact (goodGraphFiberRelations_eval K T k).trans (hT k)
      exact fun _ ha => hle ha)

lemma goodGraphFiberLift_x {A : Type*} [CommRing A] [Algebra K A]
    (T : Matrix (Fin 3) (Fin 3) A) (hT : ∀ k, goodGraphRelation A T k = 0) (i j : Fin 3) :
    goodGraphFiberLift K T hT (goodGraphFiberX K i j) = T i j :=
  MvPolynomial.aeval_X _ _

end
section
variable (K : Type*) [Field K] [NeZero (2 : K)]

lemma goodGraphFiberX_diagonal :
    goodGraphFiberX K = Matrix.diagonal (fun i => goodGraphFiberX K i i) := by
  have h2 : IsUnit (2 : GoodGraphFiberAlgebra K) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (NeZero.ne (2 : K))).map (algebraMap K (GoodGraphFiberAlgebra K))
  apply goodMatrixGraph_diagonal_of_entries _ h2
  · intro i j
    exact goodGraphFiberX_relation K (0, i, j)
  · intro i j
    exact goodGraphFiberX_relation K (1, i, j)

lemma goodGraphFiberX_three_relations :
    1 + goodGraphFiberX K 0 0 * goodGraphFiberX K 1 1 = 0 ∧
    1 + goodGraphFiberX K 0 0 * goodGraphFiberX K 2 2 = 0 ∧
    1 + 2 * goodGraphFiberX K 1 1 * goodGraphFiberX K 2 2 = 0 := by
  have h01 : goodGraphThirdEntry _ (goodGraphFiberX K) 0 1 = 0 := goodGraphFiberX_relation K (2, 0, 1)
  have h02 : goodGraphThirdEntry _ (goodGraphFiberX K) 0 2 = 0 := goodGraphFiberX_relation K (2, 0, 2)
  have h12 : goodGraphThirdEntry _ (goodGraphFiberX K) 1 2 = 0 := goodGraphFiberX_relation K (2, 1, 2)
  rw [goodGraphFiberX_diagonal, goodGraphThirdEntry_diagonal01] at h01
  rw [goodGraphFiberX_diagonal, goodGraphThirdEntry_diagonal02] at h02
  rw [goodGraphFiberX_diagonal, goodGraphThirdEntry_diagonal12] at h12
  exact ⟨h01, h02, h12⟩

end
end PfaffianDescent

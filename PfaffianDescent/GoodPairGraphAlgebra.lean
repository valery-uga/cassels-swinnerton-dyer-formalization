import PfaffianDescent.GoodGraphFiberAlgebra

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]

/-- The complete restriction equations for the first two displayed forms. -/
def goodPairGraphRelation (T : Matrix (Fin 3) (Fin 3) R)
    (k : Fin 2 × Fin 3 × Fin 3) : R :=
  if k.1 = 0 then T k.2.1 k.2.2 - T k.2.2 k.2.1
  else goodBlockEigenvalue R k.2.1 * T k.2.1 k.2.2 -
    goodBlockEigenvalue R k.2.2 * T k.2.2 k.2.1

lemma goodPairGraphRelation_diagonal (u : Fin 3 → R) (k : Fin 2 × Fin 3 × Fin 3) :
    goodPairGraphRelation R (Matrix.diagonal u) k = 0 := by
  rcases k with ⟨b, i, j⟩
  by_cases hij : i = j
  · subst j
    simp [goodPairGraphRelation]
  · simp [goodPairGraphRelation, Matrix.diagonal, hij, Ne.symm hij]

end
section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma goodPairGraphRelation_map (φ : R →+* S) (T : Matrix (Fin 3) (Fin 3) R)
    (k : Fin 2 × Fin 3 × Fin 3) :
    goodPairGraphRelation S (T.map φ) k = φ (goodPairGraphRelation R T k) := by
  by_cases h : k.1 = 0
  · simp [goodPairGraphRelation, h, Matrix.map_apply]
  · simp [goodPairGraphRelation, h, Matrix.map_apply, goodBlockEigenvalue_map]

end
section
variable (K : Type*) [CommRing K]

noncomputable def goodPairGraphRelations (k : Fin 2 × Fin 3 × Fin 3) : GoodGraphFiberPolynomial K :=
  goodPairGraphRelation _ (goodGraphFiberUniversalMatrix K) k

noncomputable def goodPairGraphIdeal : Ideal (GoodGraphFiberPolynomial K) :=
  Ideal.span (Set.range (goodPairGraphRelations K))

/-- The scheme-theoretic first-two-form locus on the split graph chart. -/
abbrev GoodPairGraphAlgebra := GoodGraphFiberPolynomial K ⧸ goodPairGraphIdeal K

noncomputable def goodPairGraphX (i j : Fin 3) : GoodPairGraphAlgebra K :=
  Ideal.Quotient.mkₐ K (goodPairGraphIdeal K) (MvPolynomial.X (i, j))

lemma goodPairGraphRelations_eval {A : Type*} [CommRing A] [Algebra K A]
    (T : Matrix (Fin 3) (Fin 3) A) (k : Fin 2 × Fin 3 × Fin 3) :
    MvPolynomial.aeval (R := K) (fun ij => T ij.1 ij.2) (goodPairGraphRelations K k) =
      goodPairGraphRelation A T k := by
  let φ : GoodGraphFiberPolynomial K →+* A :=
    (MvPolynomial.aeval (R := K) (fun ij : Fin 3 × Fin 3 => T ij.1 ij.2)).toRingHom
  have he : (goodGraphFiberUniversalMatrix K).map φ = T := by
    funext i j
    exact MvPolynomial.aeval_X _ _
  have hmap := goodPairGraphRelation_map φ (goodGraphFiberUniversalMatrix K) k
  rw [he] at hmap
  exact hmap.symm

lemma goodPairGraphX_relation (k : Fin 2 × Fin 3 × Fin 3) :
    goodPairGraphRelation (GoodPairGraphAlgebra K) (goodPairGraphX K) k = 0 := by
  have hz : Ideal.Quotient.mkₐ K (goodPairGraphIdeal K) (goodPairGraphRelations K k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, rfl⟩)
  exact (goodPairGraphRelation_map (Ideal.Quotient.mkₐ K (goodPairGraphIdeal K)).toRingHom
    (goodGraphFiberUniversalMatrix K) k).trans hz

noncomputable def goodPairGraphLift {A : Type*} [CommRing A] [Algebra K A]
    (T : Matrix (Fin 3) (Fin 3) A) (hT : ∀ k, goodPairGraphRelation A T k = 0) :
    GoodPairGraphAlgebra K →ₐ[K] A :=
  Ideal.Quotient.liftₐ (goodPairGraphIdeal K)
    (MvPolynomial.aeval (R := K) (fun ij => T ij.1 ij.2)) (by
      have hle : goodPairGraphIdeal K ≤ RingHom.ker
          (MvPolynomial.aeval (R := K) (fun ij => T ij.1 ij.2)).toRingHom := by
        apply Ideal.span_le.mpr
        rintro _ ⟨k, rfl⟩
        exact (goodPairGraphRelations_eval K T k).trans (hT k)
      exact fun _ ha => hle ha)

lemma goodPairGraphLift_x {A : Type*} [CommRing A] [Algebra K A]
    (T : Matrix (Fin 3) (Fin 3) A) (hT : ∀ k, goodPairGraphRelation A T k = 0) (i j : Fin 3) :
    goodPairGraphLift K T hT (goodPairGraphX K i j) = T i j :=
  MvPolynomial.aeval_X _ _

lemma goodPairGraphX_diagonal (h2 : IsUnit (2 : K)) :
    goodPairGraphX K = Matrix.diagonal (fun i => goodPairGraphX K i i) := by
  have h2' : IsUnit (2 : GoodPairGraphAlgebra K) := by
    simpa only [map_ofNat] using h2.map (algebraMap K (GoodPairGraphAlgebra K))
  apply goodMatrixGraph_diagonal_of_entries _ h2'
  · intro i j
    exact goodPairGraphX_relation K (0, i, j)
  · intro i j
    exact goodPairGraphX_relation K (1, i, j)

noncomputable def goodPairGraphToAffine : GoodPairGraphAlgebra K →ₐ[K] MvPolynomial (Fin 3) K :=
  goodPairGraphLift K (Matrix.diagonal MvPolynomial.X) (goodPairGraphRelation_diagonal _ _)

noncomputable def goodPairGraphFromAffine : MvPolynomial (Fin 3) K →ₐ[K] GoodPairGraphAlgebra K :=
  MvPolynomial.aeval (fun i => goodPairGraphX K i i)

lemma goodPairGraphToAffine_x (i j : Fin 3) :
    goodPairGraphToAffine K (goodPairGraphX K i j) = Matrix.diagonal MvPolynomial.X i j :=
  goodPairGraphLift_x K _ _ i j

lemma goodPairGraphFromAffine_x (i : Fin 3) :
    goodPairGraphFromAffine K (MvPolynomial.X i) = goodPairGraphX K i i :=
  MvPolynomial.aeval_X _ _

lemma goodPairGraph_to_from :
    (goodPairGraphToAffine K).comp (goodPairGraphFromAffine K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  change goodPairGraphToAffine K (goodPairGraphFromAffine K (MvPolynomial.X i)) = MvPolynomial.X i
  rw [goodPairGraphFromAffine_x, goodPairGraphToAffine_x, Matrix.diagonal_apply_eq]

lemma goodPairGraph_from_to (h2 : IsUnit (2 : K)) :
    (goodPairGraphFromAffine K).comp (goodPairGraphToAffine K) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  change goodPairGraphFromAffine K (goodPairGraphToAffine K (goodPairGraphX K i j)) = goodPairGraphX K i j
  rw [goodPairGraphToAffine_x]
  by_cases h : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, goodPairGraphFromAffine_x]
  · have hx := congrFun (congrFun (goodPairGraphX_diagonal K h2) i) j
    simp [Matrix.diagonal, h] at hx ⊢
    exact hx.symm

/-- The two isotropy conditions cut out affine three-space, with no hidden nilpotents,
over every coefficient ring in which two is invertible. -/
noncomputable def goodPairGraphEquiv (h2 : IsUnit (2 : K)) :
    GoodPairGraphAlgebra K ≃ₐ[K] MvPolynomial (Fin 3) K :=
  AlgEquiv.ofAlgHom (goodPairGraphToAffine K) (goodPairGraphFromAffine K)
    (goodPairGraph_to_from K) (goodPairGraph_from_to K h2)

end
end PfaffianDescent

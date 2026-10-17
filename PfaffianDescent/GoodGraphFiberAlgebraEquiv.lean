import PfaffianDescent.GoodGraphFiberAlgebra

namespace PfaffianDescent
section
variable (K : Type*) [Field K] [NeZero (2 : K)]

/-- Evaluation on the actual three-equation fiber algebra. -/
noncomputable def goodFiberAlgebraLift {A : Type*} [CommRing A] [Algebra K A]
    (u : Fin 3 → A)
    (hu : 1 + u 0 * u 1 = 0 ∧ 1 + u 0 * u 2 = 0 ∧ 1 + 2 * u 1 * u 2 = 0) :
    GoodFiberAlgebra K →ₐ[K] A :=
  Ideal.Quotient.liftₐ (goodFiberIdeal K) (MvPolynomial.aeval (R := K) u) (by
    have hle : goodFiberIdeal K ≤ RingHom.ker (MvPolynomial.aeval (R := K) u).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change MvPolynomial.aeval u (goodFiberRelations K i) = 0
      fin_cases i
      · simpa [goodFiberRelations] using hu.1
      · simpa [goodFiberRelations] using hu.2.1
      · simpa [goodFiberRelations, map_ofNat] using hu.2.2
    exact fun _ ha => hle ha)

lemma goodFiberAlgebraLift_x {A : Type*} [CommRing A] [Algebra K A]
    (u : Fin 3 → A)
    (hu : 1 + u 0 * u 1 = 0 ∧ 1 + u 0 * u 2 = 0 ∧ 1 + 2 * u 1 * u 2 = 0)
    (i : Fin 3) : goodFiberAlgebraLift K u hu (GoodFiberAlgebra.x (K := K) i) = u i :=
  MvPolynomial.aeval_X _ _

lemma goodGraphFiber_three_diagonal_relations (k : Fin 3 × Fin 3 × Fin 3) :
    goodGraphRelation (GoodFiberAlgebra K) (Matrix.diagonal GoodFiberAlgebra.x) k = 0 := by
  rcases k with ⟨b, i, j⟩
  fin_cases b
  · by_cases h : i = j
    · subst j; simp [goodGraphRelation]
    · simp [goodGraphRelation, Matrix.diagonal, h, Ne.symm h]
  · by_cases h : i = j
    · subst j; simp [goodGraphRelation]
    · simp [goodGraphRelation, Matrix.diagonal, h, Ne.symm h]
  · exact (goodMatrixGraph_third_iff (GoodFiberAlgebra K) GoodFiberAlgebra.x).mpr
      GoodFiberAlgebra.relations (Pi.single i 1) (Pi.single j 1)

noncomputable def goodGraphFiberToThree : GoodGraphFiberAlgebra K →ₐ[K] GoodFiberAlgebra K :=
  goodGraphFiberLift K (Matrix.diagonal GoodFiberAlgebra.x) (goodGraphFiber_three_diagonal_relations K)

noncomputable def goodGraphFiberFromThree : GoodFiberAlgebra K →ₐ[K] GoodGraphFiberAlgebra K :=
  goodFiberAlgebraLift K (fun i => goodGraphFiberX K i i) (goodGraphFiberX_three_relations K)

lemma goodGraphFiberToThree_x (i j : Fin 3) :
    goodGraphFiberToThree K (goodGraphFiberX K i j) =
      Matrix.diagonal (GoodFiberAlgebra.x (K := K)) i j :=
  goodGraphFiberLift_x K _ _ i j

lemma goodGraphFiberFromThree_x (i : Fin 3) :
    goodGraphFiberFromThree K (GoodFiberAlgebra.x (K := K) i) = goodGraphFiberX K i i :=
  goodFiberAlgebraLift_x K _ _ i

lemma goodGraphFiber_to_from :
    (goodGraphFiberToThree K).comp (goodGraphFiberFromThree K) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change goodGraphFiberToThree K (goodGraphFiberFromThree K (GoodFiberAlgebra.x i)) = GoodFiberAlgebra.x i
  rw [goodGraphFiberFromThree_x, goodGraphFiberToThree_x, Matrix.diagonal_apply_eq]

lemma goodGraphFiber_from_to :
    (goodGraphFiberFromThree K).comp (goodGraphFiberToThree K) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  change goodGraphFiberFromThree K (goodGraphFiberToThree K (goodGraphFiberX K i j)) = goodGraphFiberX K i j
  rw [goodGraphFiberToThree_x]
  by_cases h : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, goodGraphFiberFromThree_x]
  · have hx := congrFun (congrFun (goodGraphFiberX_diagonal K) i) j
    simp [Matrix.diagonal, h] at hx ⊢
    exact hx.symm

/-- The entire graph-chart fiber algebra, with its scheme structure, is the
three-equation algebra and therefore the quadratic algebra of the note. -/
noncomputable def goodGraphFiberEquiv : GoodGraphFiberAlgebra K ≃ₐ[K] GoodFiberAlgebra K :=
  AlgEquiv.ofAlgHom (goodGraphFiberToThree K) (goodGraphFiberFromThree K)
    (goodGraphFiber_to_from K) (goodGraphFiber_from_to K)

instance goodGraphFiberAlgebra_finite : Module.Finite K (GoodGraphFiberAlgebra K) :=
  (goodGraphFiberEquiv K).toLinearEquiv.symm.finiteDimensional

lemma goodGraphFiberAlgebra_finrank : Module.finrank K (GoodGraphFiberAlgebra K) = 2 := by
  rw [(goodGraphFiberEquiv K).toLinearEquiv.finrank_eq]
  exact GoodFiberAlgebra.finrank_eq_two

instance goodGraphFiberAlgebra_etale : Algebra.Etale K (GoodGraphFiberAlgebra K) :=
  Algebra.Etale.of_equiv (goodGraphFiberEquiv K).symm

instance goodGraphFiberAlgebra_reduced : IsReduced (GoodGraphFiberAlgebra K) :=
  Algebra.FormallyUnramified.isReduced_of_field K (GoodGraphFiberAlgebra K)

end
end PfaffianDescent

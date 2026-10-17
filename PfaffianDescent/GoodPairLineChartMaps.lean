import PfaffianDescent.GoodPairIncidenceAtlas
import PfaffianDescent.GoodPairChartSubmodules
import PfaffianDescent.PolynomialSchemePoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

noncomputable def goodPairFiberToGrassmannian : goodPairIncidenceFiber K ⟶ grassmannianScheme K 3 3 :=
  pullback.fst (incidenceToTriples K) (goodPairTripleSection K) ≫ incidenceToGrassmannian K

/-- The line in the `i`-th block, on each of the eight actual incidence charts. -/
noncomputable def goodMixedPairToLine (ε : Fin 3 → Bool) (i : Fin 3) :
    goodMixedPairScheme K ⟶ grassmannianScheme K 1 1 :=
  grassmannianChartEvaluation K (lineChartMatrix (MvPolynomial (Fin 3) K) (MvPolynomial.X i)) ≫
    grassmannianChartι K (lineChartPermutation (ε i))

lemma goodMixedPairToLine_toBase (ε : Fin 3 → Bool) (i : Fin 3) :
    goodMixedPairToLine K ε i ≫ grassmannianToBase K 1 1 = goodMixedPairToBase K := by
  change (grassmannianChartEvaluation K
    (lineChartMatrix (MvPolynomial (Fin 3) K) (MvPolynomial.X i)) ≫
      grassmannianChartι K (lineChartPermutation (ε i))) ≫ grassmannianToBase K 1 1 =
        Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K)))
  rw [Category.assoc, grassmannianChartι_toBase]
  exact grassmannianChartEvaluation_toBase K _

lemma goodMixedPairToGlobalFiber_toGrassmannian (ε : Fin 3 → Bool) :
    goodMixedPairToGlobalFiber K ε ≫ goodPairFiberToGrassmannian K =
      grassmannianChartEvaluation K (Matrix.diagonal (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) K)) ≫
        grassmannianChartι K (goodMixedChartPermutation ε) := by
  let p : goodPairIncidenceFiber K ⟶ incidenceScheme K :=
    pullback.fst (incidenceToTriples K) (goodPairTripleSection K)
  have hc : goodMixedPairToGlobalFiber K ε ≫ goodPairFiberToGrassmannian K =
      goodMixedPairToIncidence K ε ≫ incidenceToGrassmannian K :=
    (Category.assoc (goodMixedPairToGlobalFiber K ε) p (incidenceToGrassmannian K)).symm.trans
      (congrArg (fun q : goodMixedPairScheme K ⟶ incidenceScheme K => q ≫ incidenceToGrassmannian K)
        (goodMixedPairToGlobalFiber_toIncidence K ε))
  apply hc.trans
  change (incidenceChartEvaluation K (goodMixedPairUniversalPoint K ε) ≫
    incidenceChartι K (goodMixedChartPermutation ε)) ≫ incidenceToGrassmannian K = _
  rw [Category.assoc, incidenceChartι_toGrassmannian, ← Category.assoc,
    incidenceChartEvaluation_toGraph]
  change grassmannianChartEvaluation K
    (LinearMap.toMatrix' (Matrix.toLin' (Matrix.diagonal MvPolynomial.X))) ≫ _ = _
  rw [LinearMap.toMatrix'_toLin']

variable {A : Type u} [CommRing A] [Algebra K A]

lemma goodMixedPairEvaluation_toLine (ε : Fin 3 → Bool) (u : Fin 3 → A) (i : Fin 3) :
    polynomialSchemeEvaluation K (Fin 3) u ≫ goodMixedPairToLine K ε i =
      grassmannianChartEvaluation K (lineChartMatrix A (u i)) ≫ grassmannianChartι K (lineChartPermutation (ε i)) := by
  change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) u).toRingHom) ≫
    (grassmannianChartEvaluation K (lineChartMatrix (MvPolynomial (Fin 3) K) (MvPolynomial.X i)) ≫
      grassmannianChartι K (lineChartPermutation (ε i))) = _
  rw [← Category.assoc]
  rw [grassmannianChartEvaluation_map]
  have he : (lineChartMatrix (MvPolynomial (Fin 3) K) (MvPolynomial.X i)).map
      (MvPolynomial.aeval (R := K) u) = lineChartMatrix A (u i) := by
    funext j k
    exact MvPolynomial.aeval_X u i
  rw [he]

lemma goodMixedPairEvaluation_toGrassmannian (ε : Fin 3 → Bool) (u : Fin 3 → A) :
    (polynomialSchemeEvaluation K (Fin 3) u ≫ goodMixedPairToGlobalFiber K ε) ≫ goodPairFiberToGrassmannian K =
      grassmannianChartEvaluation K (Matrix.diagonal u) ≫ grassmannianChartι K (goodMixedChartPermutation ε) := by
  let f : Spec (.of A) ⟶ goodMixedPairScheme K := polynomialSchemeEvaluation K (Fin 3) u
  have hc := (Category.assoc f (goodMixedPairToGlobalFiber K ε) (goodPairFiberToGrassmannian K)).trans
    (congrArg (fun q : goodMixedPairScheme K ⟶ grassmannianScheme K 3 3 => f ≫ q)
      (goodMixedPairToGlobalFiber_toGrassmannian K ε))
  apply hc.trans
  change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) u).toRingHom) ≫
    (grassmannianChartEvaluation K (Matrix.diagonal (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) K)) ≫
      grassmannianChartι K (goodMixedChartPermutation ε)) = _
  rw [← Category.assoc]
  rw [grassmannianChartEvaluation_map]
  have he : (Matrix.diagonal (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) K)).map
      (MvPolynomial.aeval (R := K) u) = Matrix.diagonal u := by
    funext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, h]
  rw [he]

/-- If two actual incidence chart points agree, their three line images agree. -/
lemma goodMixedPairEvaluation_line_eq (ε δ : Fin 3 → Bool) (u v : Fin 3 → A)
    (h : polynomialSchemeEvaluation K (Fin 3) u ≫ goodMixedPairToGlobalFiber K ε =
      polynomialSchemeEvaluation K (Fin 3) v ≫ goodMixedPairToGlobalFiber K δ) (i : Fin 3) :
    polynomialSchemeEvaluation K (Fin 3) u ≫ goodMixedPairToLine K ε i =
      polynomialSchemeEvaluation K (Fin 3) v ≫ goodMixedPairToLine K δ i := by
  have he := congrArg (fun f => f ≫ goodPairFiberToGrassmannian K) h
  rw [goodMixedPairEvaluation_toGrassmannian, goodMixedPairEvaluation_toGrassmannian] at he
  have hW := (grassmannianChartEvaluation_eq_iff_submodule K
    (goodMixedChartPermutation ε) (goodMixedChartPermutation δ) (Matrix.diagonal u) (Matrix.diagonal v)).mp he
  rw [goodMixedPairEvaluation_toLine, goodMixedPairEvaluation_toLine]
  exact (grassmannianChartEvaluation_eq_iff_submodule K _ _ _ _).mpr
    (goodMixedChartSubmodule_components_eq A ε δ u v hW i)

end
end PfaffianDescent

import PfaffianDescent.GoodPairFiberGlobalMap

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

lemma goodPairGraph_incidence_coordinates_surjective :
    Function.Surjective (MvPolynomial.aeval (R := K)
      (incidenceGraphPointCoordinates (GoodPairGraphAlgebra K) (goodPairGraphIncidencePoint K))) := by
  let φ : IncidenceGraphRing K →ₐ[K] GoodPairGraphAlgebra K :=
    MvPolynomial.aeval (R := K)
      (incidenceGraphPointCoordinates (GoodPairGraphAlgebra K) (goodPairGraphIncidencePoint K))
  have he : φ.comp (MvPolynomial.rename (R := K)
      (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex)) =
      Ideal.Quotient.mkₐ K (goodPairGraphIdeal K) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    change φ ((MvPolynomial.rename Sum.inl) (MvPolynomial.X (i, j))) = goodPairGraphX K i j
    rw [MvPolynomial.rename_X]
    change MvPolynomial.aeval _ (MvPolynomial.X (Sum.inl (i, j))) = goodPairGraphX K i j
    rw [MvPolynomial.aeval_X]
    change LinearMap.toMatrix' (Matrix.toLin' (goodPairGraphX K)) i j = goodPairGraphX K i j
    exact congrFun (congrFun (LinearMap.toMatrix'_toLin' (Matrix.of (goodPairGraphX K))) i) j
  intro q
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨MvPolynomial.rename (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex) p, ?_⟩
  exact (AlgHom.congr_fun he p).trans hp

/-- The computed fiber embeds as a closed subscheme of the actual incidence chart. -/
instance goodPairGraphToIncidenceChart_closed : IsClosedImmersion (goodPairGraphToIncidenceChart K) :=
  IsClosedImmersion.spec_of_surjective _ (goodPairGraph_incidence_coordinates_surjective K)

end
end PfaffianDescent

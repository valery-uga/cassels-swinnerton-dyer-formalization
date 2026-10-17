import PfaffianDescent.GoodFiberGlobalMap

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

lemma goodGraphFiber_incidence_coordinates_surjective :
    Function.Surjective (MvPolynomial.aeval (R := K)
      (incidenceGraphPointCoordinates (GoodGraphFiberAlgebra K) (goodGraphFiberIncidencePoint K))) := by
  let φ : IncidenceGraphRing K →ₐ[K] GoodGraphFiberAlgebra K :=
    MvPolynomial.aeval (R := K)
      (incidenceGraphPointCoordinates (GoodGraphFiberAlgebra K) (goodGraphFiberIncidencePoint K))
  have he : φ.comp (MvPolynomial.rename (R := K)
      (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex)) =
      Ideal.Quotient.mkₐ K (goodGraphFiberIdeal K) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    change φ ((MvPolynomial.rename Sum.inl) (MvPolynomial.X (i, j))) = goodGraphFiberX K i j
    rw [MvPolynomial.rename_X]
    change MvPolynomial.aeval _ (MvPolynomial.X (Sum.inl (i, j))) = goodGraphFiberX K i j
    rw [MvPolynomial.aeval_X]
    change LinearMap.toMatrix' (Matrix.toLin' (goodGraphFiberX K)) i j = goodGraphFiberX K i j
    exact congrFun (congrFun (LinearMap.toMatrix'_toLin' (Matrix.of (goodGraphFiberX K))) i) j
  intro q
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨MvPolynomial.rename (Sum.inl : Fin 3 × Fin 3 → IncidenceGraphIndex) p, ?_⟩
  exact (AlgHom.congr_fun he p).trans hp

/-- The computed fiber embeds as a closed subscheme of the actual incidence chart. -/
instance goodGraphFiberToIncidenceChart_closed : IsClosedImmersion (goodGraphFiberToIncidenceChart K) :=
  IsClosedImmersion.spec_of_surjective _ (goodGraphFiber_incidence_coordinates_surjective K)

end
end PfaffianDescent

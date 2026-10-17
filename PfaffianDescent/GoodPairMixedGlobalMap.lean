import PfaffianDescent.GoodPairMixedIncidence
import PfaffianDescent.GoodPairFiberGlobalMap

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

noncomputable def goodMixedPairScheme : Scheme.{u} := Spec (.of (MvPolynomial (Fin 3) K))

noncomputable def goodMixedPairToBase : goodMixedPairScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K)))

noncomputable def goodMixedPairToIncidenceChart (ε : Fin 3 → Bool) :
    goodMixedPairScheme K ⟶ incidenceGraphScheme K :=
  incidenceChartEvaluation K (goodMixedPairUniversalPoint K ε)

lemma goodMixedPairToIncidenceChart_triples (ε : Fin 3 → Bool) :
    goodMixedPairToIncidenceChart K ε ≫ incidenceChartToTriples K (goodMixedChartPermutation ε) =
      goodMixedPairToBase K ≫ goodPairTripleSection K := by
  have hc := goodMixedPairAffinePoint_coefficients (MvPolynomial (Fin 3) K) ε MvPolynomial.X
  exact (incidenceChartEvaluation_toTriples K (goodMixedChartPermutation ε)
    (goodMixedPairUniversalPoint K ε)).trans
    ((congrArg (fun c : AlternatingTripleIndex → MvPolynomial (Fin 3) K =>
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) c).toRingHom)) hc).trans
        (goodPairTripleSection_baseChange K (A := MvPolynomial (Fin 3) K)).symm)

noncomputable def goodMixedPairToIncidence (ε : Fin 3 → Bool) :
    goodMixedPairScheme K ⟶ incidenceScheme K :=
  goodMixedPairToIncidenceChart K ε ≫ incidenceChartι K (goodMixedChartPermutation ε)

lemma goodMixedPairToIncidence_triples (ε : Fin 3 → Bool) :
    goodMixedPairToIncidence K ε ≫ incidenceToTriples K = goodMixedPairToBase K ≫ goodPairTripleSection K := by
  rw [goodMixedPairToIncidence, Category.assoc, incidenceChartι_toTriples]
  exact goodMixedPairToIncidenceChart_triples K ε

noncomputable def goodMixedPairToGlobalFiber (ε : Fin 3 → Bool) :
    goodMixedPairScheme K ⟶ goodPairIncidenceFiber K :=
  pullback.lift (goodMixedPairToIncidence K ε) (goodMixedPairToBase K)
    (goodMixedPairToIncidence_triples K ε)

lemma goodMixedPairToGlobalFiber_toBase (ε : Fin 3 → Bool) :
    goodMixedPairToGlobalFiber K ε ≫ goodPairIncidenceFiberToBase K = goodMixedPairToBase K :=
  pullback.lift_snd _ _ _

lemma goodMixedPairToGlobalFiber_toIncidence (ε : Fin 3 → Bool) :
    goodMixedPairToGlobalFiber K ε ≫ pullback.fst (incidenceToTriples K) (goodPairTripleSection K) =
      goodMixedPairToIncidence K ε := pullback.lift_fst _ _ _

lemma goodMixedPair_incidence_coordinates_surjective (ε : Fin 3 → Bool) :
    Function.Surjective (MvPolynomial.aeval (R := K)
      (incidenceGraphPointCoordinates (MvPolynomial (Fin 3) K) (goodMixedPairUniversalPoint K ε))) := by
  let φ : IncidenceGraphRing K →ₐ[K] MvPolynomial (Fin 3) K :=
    MvPolynomial.aeval (R := K)
      (incidenceGraphPointCoordinates (MvPolynomial (Fin 3) K) (goodMixedPairUniversalPoint K ε))
  let d : Fin 3 → IncidenceGraphIndex := fun i => Sum.inl (i, i)
  have he : φ.comp (MvPolynomial.rename (R := K) d) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    change φ ((MvPolynomial.rename d) (MvPolynomial.X i)) = MvPolynomial.X i
    rw [MvPolynomial.rename_X]
    change MvPolynomial.aeval _ (MvPolynomial.X (Sum.inl (i, i))) = MvPolynomial.X i
    rw [MvPolynomial.aeval_X]
    change LinearMap.toMatrix' (Matrix.toLin' (Matrix.diagonal MvPolynomial.X)) i i = MvPolynomial.X i
    rw [LinearMap.toMatrix'_toLin', Matrix.diagonal_apply_eq]
  intro q
  exact ⟨MvPolynomial.rename d q, AlgHom.congr_fun he q⟩

instance goodMixedPairToIncidenceChart_closed (ε : Fin 3 → Bool) :
    IsClosedImmersion (goodMixedPairToIncidenceChart K ε) :=
  IsClosedImmersion.spec_of_surjective _ (goodMixedPair_incidence_coordinates_surjective K ε)

end
end PfaffianDescent

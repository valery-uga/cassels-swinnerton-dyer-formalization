import PfaffianDescent.GoodPairChartForms
import PfaffianDescent.GoodPairGraphScheme
import PfaffianDescent.IncidenceAlgebraPoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A]

/-- The displayed triple has the same coefficients after every base change. -/
lemma goodPairTripleSection_baseChange :
    Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫ goodPairTripleSection K =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients A)).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients K)).toRingHom) = _
  rw [← Spec.map_comp]
  have he : (Algebra.ofId K A).comp
      (MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients K)) =
      MvPolynomial.aeval (R := K) (goodPairTripleSchemeCoefficients A) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    exact (goodPairTripleSchemeCoefficients_map (algebraMap K A) j).symm
  exact congrArg (fun φ : AlternatingTripleRing K →ₐ[K] A => Spec.map (CommRingCat.ofHom φ.toRingHom)) he

end
section
variable (K : Type u) [CommRing K]

/-- The first-two-form graph-chart scheme maps to the actual incidence chart. -/
noncomputable def goodPairGraphToIncidenceChart : goodPairGraphScheme K ⟶ incidenceGraphScheme K :=
  incidenceChartEvaluation K (goodPairGraphIncidencePoint K)

lemma goodPairGraphToIncidenceChart_triples :
    goodPairGraphToIncidenceChart K ≫ incidenceChartToTriples K goodChartPermutation =
      goodPairGraphToBase K ≫ goodPairTripleSection K := by
  have hc : incidenceOriginalCoefficients goodChartPermutation (goodPairGraphIncidencePoint K) =
      goodPairTripleSchemeCoefficients (GoodPairGraphAlgebra K) := by
    funext j
    exact goodPairGraphIncidencePoint_coefficients K j
  exact (incidenceChartEvaluation_toTriples K goodChartPermutation (goodPairGraphIncidencePoint K)).trans
    ((congrArg (fun c : AlternatingTripleIndex → GoodPairGraphAlgebra K =>
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) c).toRingHom)) hc).trans
        (goodPairTripleSection_baseChange K (A := GoodPairGraphAlgebra K)).symm)

/-- The first-two-form graph scheme maps to the full global common-isotropic incidence. -/
noncomputable def goodPairGraphToIncidence : goodPairGraphScheme K ⟶ incidenceScheme K :=
  goodPairGraphToIncidenceChart K ≫ incidenceChartι K goodChartPermutation

lemma goodPairGraphToIncidence_triples :
    goodPairGraphToIncidence K ≫ incidenceToTriples K = goodPairGraphToBase K ≫ goodPairTripleSection K := by
  rw [goodPairGraphToIncidence, Category.assoc, incidenceChartι_toTriples]
  exact goodPairGraphToIncidenceChart_triples K

/-- The map from the computed first-two-form scheme to the actual scheme-theoretic good fiber. -/
noncomputable def goodPairGraphToGlobalFiber : goodPairGraphScheme K ⟶ goodPairIncidenceFiber K :=
  pullback.lift (goodPairGraphToIncidence K) (goodPairGraphToBase K)
    (goodPairGraphToIncidence_triples K)

lemma goodPairGraphToGlobalFiber_toBase :
    goodPairGraphToGlobalFiber K ≫ goodPairIncidenceFiberToBase K = goodPairGraphToBase K :=
  pullback.lift_snd _ _ _

lemma goodPairGraphToGlobalFiber_toIncidence :
    goodPairGraphToGlobalFiber K ≫ pullback.fst (incidenceToTriples K) (goodPairTripleSection K) =
      goodPairGraphToIncidence K :=
  pullback.lift_fst _ _ _

end
end PfaffianDescent

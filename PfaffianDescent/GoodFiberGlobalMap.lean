import PfaffianDescent.GoodChartForms
import PfaffianDescent.GoodGraphFiberScheme
import PfaffianDescent.IncidenceAlgebraPoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A]

/-- The displayed triple has the same coefficients after every base change. -/
lemma goodTripleSection_baseChange :
    Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫ goodTripleSection K =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (R := K) (goodTripleSchemeCoefficients A)).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := K) (goodTripleSchemeCoefficients K)).toRingHom) = _
  rw [← Spec.map_comp]
  have he : (Algebra.ofId K A).comp
      (MvPolynomial.aeval (R := K) (goodTripleSchemeCoefficients K)) =
      MvPolynomial.aeval (R := K) (goodTripleSchemeCoefficients A) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    exact (goodTripleSchemeCoefficients_map (algebraMap K A) j).symm
  exact congrArg (fun φ : AlternatingTripleRing K →ₐ[K] A => Spec.map (CommRingCat.ofHom φ.toRingHom)) he

end
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

/-- The finite étale graph-chart scheme maps to the actual incidence chart. -/
noncomputable def goodGraphFiberToIncidenceChart : goodGraphFiberScheme K ⟶ incidenceGraphScheme K :=
  incidenceChartEvaluation K (goodGraphFiberIncidencePoint K)

lemma goodGraphFiberToIncidenceChart_triples :
    goodGraphFiberToIncidenceChart K ≫ incidenceChartToTriples K goodChartPermutation =
      goodGraphFiberToBase K ≫ goodTripleSection K := by
  have hc : incidenceOriginalCoefficients goodChartPermutation (goodGraphFiberIncidencePoint K) =
      goodTripleSchemeCoefficients (GoodGraphFiberAlgebra K) := by
    funext j
    exact goodGraphFiberIncidencePoint_coefficients K j
  exact (incidenceChartEvaluation_toTriples K goodChartPermutation (goodGraphFiberIncidencePoint K)).trans
    ((congrArg (fun c : AlternatingTripleIndex → GoodGraphFiberAlgebra K =>
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) c).toRingHom)) hc).trans
        (goodTripleSection_baseChange K (A := GoodGraphFiberAlgebra K)).symm)

/-- The two-point graph scheme maps to the full global common-isotropic incidence. -/
noncomputable def goodGraphFiberToIncidence : goodGraphFiberScheme K ⟶ incidenceScheme K :=
  goodGraphFiberToIncidenceChart K ≫ incidenceChartι K goodChartPermutation

lemma goodGraphFiberToIncidence_triples :
    goodGraphFiberToIncidence K ≫ incidenceToTriples K = goodGraphFiberToBase K ≫ goodTripleSection K := by
  rw [goodGraphFiberToIncidence, Category.assoc, incidenceChartι_toTriples]
  exact goodGraphFiberToIncidenceChart_triples K

/-- The map from the computed degree-two scheme to the actual scheme-theoretic good fiber. -/
noncomputable def goodGraphFiberToGlobalFiber : goodGraphFiberScheme K ⟶ goodIncidenceFiber K :=
  pullback.lift (goodGraphFiberToIncidence K) (goodGraphFiberToBase K)
    (goodGraphFiberToIncidence_triples K)

lemma goodGraphFiberToGlobalFiber_toBase :
    goodGraphFiberToGlobalFiber K ≫ goodIncidenceFiberToBase K = goodGraphFiberToBase K :=
  pullback.lift_snd _ _ _

lemma goodGraphFiberToGlobalFiber_toIncidence :
    goodGraphFiberToGlobalFiber K ≫ pullback.fst (incidenceToTriples K) (goodTripleSection K) =
      goodGraphFiberToIncidence K :=
  pullback.lift_fst _ _ _

end
end PfaffianDescent

import PfaffianDescent.PolynomialMapPresentation
import PfaffianDescent.SquareJacobianOpen
import PfaffianDescent.GoodChartFiberCartesian

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
universe u

/-- Source and target coordinate sets both have cardinality forty-five. -/
noncomputable def incidenceCoordinateEquiv : AlternatingTripleIndex ≃ IncidenceGraphIndex :=
  (Fintype.equivFinOfCardEq alternatingTripleIndex_card).trans
    (Fintype.equivFinOfCardEq incidenceGraphIndex_card).symm

section
variable (K : Type u) [CommRing K]

noncomputable abbrev goodChartAlgebra : Algebra (AlternatingTripleRing K) (IncidenceGraphRing K) :=
  (MvPolynomial.aeval (R := K)
    (incidenceOriginalCoefficients goodChartPermutation (incidenceGraphUniversal K))).toAlgebra

attribute [local instance] goodChartAlgebra

instance goodChartScalarTower : IsScalarTower K (AlternatingTripleRing K) (IncidenceGraphRing K) :=
  IsScalarTower.of_algebraMap_eq' (MvPolynomial.aeval (R := K)
    (incidenceOriginalCoefficients goodChartPermutation (incidenceGraphUniversal K))).comp_algebraMap.symm

noncomputable def goodChartSquarePresentation :
    Algebra.PreSubmersivePresentation (AlternatingTripleRing K) (IncidenceGraphRing K)
      IncidenceGraphIndex AlternatingTripleIndex :=
  polynomialMapSquarePresentation K _ _ incidenceCoordinateEquiv

lemma goodChartSquarePresentation_dimension : (goodChartSquarePresentation K).dimension = 0 :=
  polynomialMapSquarePresentation_dimension K _ _ incidenceCoordinateEquiv

/-- The Jacobian determinant of the actual chart projection. -/
noncomputable def goodChartJacobian : IncidenceGraphRing K := (goodChartSquarePresentation K).jacobian

/-- The projection is étale after inverting its Jacobian. -/
lemma goodChartJacobian_etale :
    Algebra.Etale (AlternatingTripleRing K) (Localization.Away (goodChartJacobian K)) :=
  squarePresentation_etale_away_jacobian (goodChartSquarePresentation K)
    (goodChartSquarePresentation_dimension K)

noncomputable abbrev goodTripleBaseAlgebra : Algebra (AlternatingTripleRing K) K :=
  (MvPolynomial.aeval (R := K) (goodTripleSchemeCoefficients K)).toAlgebra

attribute [local instance] goodTripleBaseAlgebra

/-- Use the chart projection, rather than coefficientwise scalar multiplication, on its polynomial ring. -/
noncomputable abbrev goodChartModule : Module (AlternatingTripleRing K) (IncidenceGraphRing K) :=
  (goodChartAlgebra K).toModule

attribute [local instance] goodChartModule

abbrev GoodChartTensorFiber := K ⊗[AlternatingTripleRing K] IncidenceGraphRing K

noncomputable def goodChartTensorToChart : Spec (.of (GoodChartTensorFiber K)) ⟶ incidenceGraphScheme K :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : IncidenceGraphRing K →ₐ[AlternatingTripleRing K]
      GoodChartTensorFiber K).toRingHom)

noncomputable def goodChartTensorToBase : Spec (.of (GoodChartTensorFiber K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (GoodChartTensorFiber K)))

lemma goodChartTensor_isPullback :
    IsPullback (goodChartTensorToChart K) (goodChartTensorToBase K)
      (incidenceChartToTriples K goodChartPermutation) (goodTripleSection K) := by
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (AlternatingTripleRing K) K (IncidenceGraphRing K))).flip

end
section
variable (K : Type u) [Field K] [NeZero (2 : K)]
attribute [local instance] goodChartAlgebra goodTripleBaseAlgebra goodChartModule

noncomputable def goodChartTensorFiberIso :
    Spec (.of (GoodChartTensorFiber K)) ≅ goodGraphFiberScheme K :=
  (goodChartTensor_isPullback K).isoIsPullback _ _ (goodGraphFiber_chart_isPullback K)

lemma goodChartTensorFiberIso_toBase :
    (goodChartTensorFiberIso K).hom ≫ goodGraphFiberToBase K = goodChartTensorToBase K :=
  (goodChartTensor_isPullback K).isoIsPullback_hom_snd _ _ (goodGraphFiber_chart_isPullback K)

lemma goodChartTensorFiberIso_toChart :
    (goodChartTensorFiberIso K).hom ≫ goodGraphFiberToIncidenceChart K = goodChartTensorToChart K :=
  (goodChartTensor_isPullback K).isoIsPullback_hom_fst _ _ (goodGraphFiber_chart_isPullback K)

instance goodChartTensorFiber_etale : Algebra.Etale K (GoodChartTensorFiber K) := by
  have he : Etale ((goodChartTensorFiberIso K).hom ≫ goodGraphFiberToBase K) := inferInstance
  have ht : Etale (goodChartTensorToBase K) := goodChartTensorFiberIso_toBase K ▸ he
  exact RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp ht)

/-- The Jacobian is invertible at every point of the displayed fiber. -/
lemma goodChartJacobian_fiber_isUnit :
    IsUnit (1 ⊗ₜ[AlternatingTripleRing K] goodChartJacobian K : GoodChartTensorFiber K) :=
  presentation_fiber_jacobian_isUnit (goodChartSquarePresentation K) K

end
end PfaffianDescent

import PfaffianDescent.LineGrassmannianProjCharts
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundGridSquare
import AllCharacteristics.ProjectiveCoefficientMap

/-! # Literal polynomial chart coefficient square for the ground projective plane -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceProjectiveChartPolynomialIso
    {K : Type u} [CommRing K] {σ : Type} (j : σ) :
    Spec (.of (MvPolynomial {i : σ // i ≠ j} K)) ≅
      Spec (.of (ChartRing (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) j)) :=
  Scheme.Spec.mapIso (chartPolynomialEquiv (R := K) j).toCommRingCatIso.symm.op

theorem serreIncidenceProjectiveChartPolynomial_coefficient
    {K E : Type u} [Field K] [Field E] [Algebra K E] {σ : Type} (j : σ) :
    let I := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    let J := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E))
    (chartCoefficientMap (algebraMap K E) I J (by
      change (⊥ : Ideal (MvPolynomial σ K)).map (MvPolynomial.map (algebraMap K E)) = ⊥
      exact Ideal.map_bot) j).comp
      (chartPolynomialEquiv (R := K) j).toRingHom =
    (chartPolynomialEquiv (R := E) j).toRingHom.comp (MvPolynomial.map (algebraMap K E)) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      chartPolynomialEquiv_C, MvPolynomial.map_C]
    exact chartCoefficientMap_baseMap _ _ _ _ j k
  · intro i
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      projectiveChartPolynomialEquiv_X, MvPolynomial.map_X]
    exact chartCoefficientMap_coordinate _ _ _ _ j i.val

theorem serreIncidenceProjectiveChartPolynomial_coefficient_square
    {K E : Type u} [Field K] [Field E] [Algebra K E] {σ : Type} (j : σ) :
    let I := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    let J := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E))
    (serreIncidenceProjectiveChartPolynomialIso (K := E) j).hom ≫
      Spec.map (CommRingCat.ofHom (chartCoefficientMap (algebraMap K E) I J (by
        change (⊥ : Ideal (MvPolynomial σ K)).map (MvPolynomial.map (algebraMap K E)) = ⊥
        exact Ideal.map_bot) j)) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap K E))) ≫
      (serreIncidenceProjectiveChartPolynomialIso (K := K) j).hom := by
  simp only [serreIncidenceProjectiveChartPolynomialIso, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h := serreIncidenceProjectiveChartPolynomial_coefficient (K := K) (E := E) j
  apply RingHom.ext
  intro p
  have hp := RingHom.congr_fun h ((chartPolynomialEquiv (R := K) j).symm p)
  apply (chartPolynomialEquiv (R := E) j).injective
  simpa using hp

end PfaffianDescent

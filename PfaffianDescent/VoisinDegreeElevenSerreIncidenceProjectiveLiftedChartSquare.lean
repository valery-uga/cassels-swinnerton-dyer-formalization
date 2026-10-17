import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProjectiveLiftedChartCoordinates

/-! # Universe-compatible literal ground projective chart coordinates -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceProjectiveLiftedChartPolynomial_coefficient
    {K E : Type u} [Field K] [Field E] [Algebra K E] {σ : Type} (j : σ) :
    let I := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    let J := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E))
    (chartCoefficientMap (algebraMap K E) I J (by
      change (⊥ : Ideal (MvPolynomial σ K)).map (MvPolynomial.map (algebraMap K E)) = ⊥
      exact Ideal.map_bot) j).comp
      (serreIncidenceProjectiveLiftedChartPolynomialEquiv (K := K) j).toRingHom =
    (serreIncidenceProjectiveLiftedChartPolynomialEquiv (K := E) j).toRingHom.comp
      (MvPolynomial.map (algebraMap K E)) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      serreIncidenceProjectiveLiftedChartPolynomialEquiv_C, MvPolynomial.map_C]
    exact chartCoefficientMap_baseMap _ _ _ _ j k
  · intro i
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      serreIncidenceProjectiveLiftedChartPolynomialEquiv_X, MvPolynomial.map_X]
    exact chartCoefficientMap_coordinate _ _ _ _ j i.down.val

theorem serreIncidenceProjectiveLiftedChartPolynomial_coefficient_square
    {K E : Type u} [Field K] [Field E] [Algebra K E] {σ : Type} (j : σ) :
    let I := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    let J := (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E))
    (serreIncidenceProjectiveLiftedChartPolynomialIso (K := E) j).hom ≫
      Spec.map (CommRingCat.ofHom (chartCoefficientMap (algebraMap K E) I J (by
        change (⊥ : Ideal (MvPolynomial σ K)).map (MvPolynomial.map (algebraMap K E)) = ⊥
        exact Ideal.map_bot) j)) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap K E))) ≫
      (serreIncidenceProjectiveLiftedChartPolynomialIso (K := K) j).hom := by
  simp only [serreIncidenceProjectiveLiftedChartPolynomialIso, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Spec_map]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h := serreIncidenceProjectiveLiftedChartPolynomial_coefficient (K := K) (E := E) j
  apply RingHom.ext
  intro p
  have hp := RingHom.congr_fun h
    ((serreIncidenceProjectiveLiftedChartPolynomialEquiv (K := K) j).symm p)
  apply (serreIncidenceProjectiveLiftedChartPolynomialEquiv (K := E) j).injective
  simpa using hp

end PfaffianDescent

import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeAmbientChart

/-! # Exact configuration and normalized-coordinate projections on native charts -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem serreIncidenceNativeAmbientChartIso_hom_fst
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) (j : Fin 9) :
    (serreIncidenceNativeAmbientChartIso b j).hom ≫
      pullback.fst b (Spec.map (CommRingCat.ofHom (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j))) =
    Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) j)) ≫ B.isoSpec.inv := by
  simp [serreIncidenceNativeAmbientChartIso, pullback.map, Category.assoc,
    IsPullback.isoPullback_hom_snd]

@[reassoc]
theorem serreIncidenceNativeAmbientChartIso_hom_snd
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) (j : Fin 9) :
    (serreIncidenceNativeAmbientChartIso b j).hom ≫
      pullback.snd b (Spec.map (CommRingCat.ofHom (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j))) =
    Spec.map (CommRingCat.ofHom (chartCoefficientMap (affineFunctionHom b)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp) j)) := by
  simp [serreIncidenceNativeAmbientChartIso, pullback.map, Category.assoc,
    IsPullback.isoPullback_hom_fst]

end PfaffianDescent

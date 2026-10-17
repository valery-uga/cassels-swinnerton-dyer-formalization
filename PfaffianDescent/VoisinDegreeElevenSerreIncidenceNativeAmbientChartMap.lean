import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeAmbientProjection
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeAmbientChartProjection

/-! # Actual relative coordinate charts commute with the actual product ambient map -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceNativeAmbientChartToProduct
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) (j : Fin 9) :
    pullback b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j))) ⟶
    pullback b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ chartι _ j) (by
    rw [Category.assoc, chartι_toBase]
    exact pullback.condition)

theorem serreIncidenceNativeAmbientChart_commutes
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) (j : Fin 9) :
    chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) j ≫
      (serreIncidenceNativeAmbientProjectiveIso b).hom =
    (serreIncidenceNativeAmbientChartIso b j).hom ≫
      serreIncidenceNativeAmbientChartToProduct b j := by
  apply pullback.hom_ext
  · simp only [Category.assoc, serreIncidenceNativeAmbientProjectiveIso_hom_fst,
      serreIncidenceNativeAmbientChartToProduct, pullback.lift_fst,
      serreIncidenceNativeAmbientChartIso_hom_fst]
    rw [← Category.assoc, chartι_toBase]
  · simp only [Category.assoc, serreIncidenceNativeAmbientProjectiveIso_hom_snd,
      serreIncidenceNativeAmbientChartToProduct, pullback.lift_snd]
    rw [← Category.assoc, serreIncidenceNativeAmbientChartIso_hom_snd]
    exact chartι_projectiveCoefficientMap (affineFunctionHom b)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp) j

end PfaffianDescent

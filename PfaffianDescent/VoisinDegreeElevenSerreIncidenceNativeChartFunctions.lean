import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeAmbientChartProjection
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSpecFunctions

/-! # Actual relative chart functions are literal normalized ring coordinates -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceNativeAmbientChart_configuration_function
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) (j : Fin 9) (a : Γ(B, ⊤)) :
    (serreIncidenceNativeAmbientChartIso b j).hom.appTop
      ((pullback.fst b (Spec.map (CommRingCat.ofHom (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j)))).appTop a) =
    (Scheme.ΓSpecIso (.of (ChartRing (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) j))).inv
      (chartBaseMap (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) j a) := by
  exact serreIncidenceAffineConfiguration_function b _
    (serreIncidenceNativeAmbientChartIso b j).hom
    (chartBaseMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) j)
    (serreIncidenceNativeAmbientChartIso_hom_fst b j) a

end PfaffianDescent

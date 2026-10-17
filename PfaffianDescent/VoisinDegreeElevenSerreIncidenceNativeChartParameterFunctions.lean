import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeChartFunctions

/-! # Literal normalized parameter ratios on actual relative configuration charts -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceNativeAmbientChart_parameter_function
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) (j k : Fin 9) :
    (serreIncidenceNativeAmbientChartIso b j).hom.appTop
      ((pullback.snd b (Spec.map (CommRingCat.ofHom (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j)))).appTop
        ((Scheme.ΓSpecIso (.of (ChartRing (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 9) K)) j))).inv
            (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j k))) =
    (Scheme.ΓSpecIso (.of (ChartRing (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) j))).inv
      (chartCoordinate (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) j k) := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K) := ⊥
  let J : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)) := ⊥
  have hIJ : I.toIdeal.map (MvPolynomial.map (affineFunctionHom b)) = J.toIdeal := by
    change (⊥ : Ideal (MvPolynomial (Fin 9) K)).map
      (MvPolynomial.map (affineFunctionHom b)) = ⊥
    exact Ideal.map_bot
  let φ := chartCoefficientMap (affineFunctionHom b) I J hIJ j
  have h := congrArg Scheme.Hom.appTop
    (serreIncidenceNativeAmbientChartIso_hom_snd b j)
  rw [Scheme.Hom.comp_appTop] at h
  exact (congrArg (fun f => f ((Scheme.ΓSpecIso (.of (ChartRing I j))).inv
      (chartCoordinate I j k))) h).trans
    ((serreIncidenceSpecMap_ΓSpec_inv φ (chartCoordinate I j k)).trans
      (congrArg (fun q => (Scheme.ΓSpecIso (.of (ChartRing J j))).inv q)
        (chartCoefficientMap_coordinate (affineFunctionHom b) I J hIJ j k)))

end PfaffianDescent

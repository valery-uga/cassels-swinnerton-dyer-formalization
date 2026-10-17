import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeAmbientProjective

/-! # Literal relative normalized charts over the actual affine configuration -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceNativeAmbientChartIso
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) (j : Fin 9) :
    Spec (.of (ChartRing (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) j)) ≅
    pullback b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j))) :=
  (isPullback_chartCoefficientMap (affineFunctionHom b)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp) j).isoPullback ≪≫
  pullbackSymmetry _ _ ≪≫
  asIso (pullback.map _ _ b _ B.isoSpec.inv (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using (serreIncidenceAffineBase_isoSpec_inv b).symm)
    (by simp))

end PfaffianDescent

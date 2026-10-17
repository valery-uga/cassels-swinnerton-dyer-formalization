import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointEvaluationDistinct
import AllCharacteristics.OrderedConfigurationFieldPoints

/-! The actual surjective Serre evaluator constructs its actual ordered
three-point configuration. Distinctness is proved internally. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualEvaluation_exists_orderedConfiguration
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of F)) [IsSeparated base]
    (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (r : Fin 3 → (Spec (.of E) ⟶ X))
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (honto : Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base r hr (show X.Modules from e.E))) :
    ∃ c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver base 3).left,
      c ≫ (orderedFamilyConfigurationOver base 3).hom =
        Spec.map (CommRingCat.ofHom (algebraMap F E)) ∧
      ∀ i, (c ≫ Over.Hom.left (orderedFamilyConfigurationι base 3)) ≫
        (orderedFamilyCoordinate base 3 i).left = r i := by
  apply exists_orderedConfigurationFieldPoint base 3
    (Spec.map (CommRingCat.ofHom (algebraMap F E))) r hr
  intro i j hij heq
  exact hij (cubicClosedPointSerreSurfaceJetCotangent_actualEvaluation_points_injective
    base e C r hr honto heq)

end PfaffianDescent

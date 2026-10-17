import PfaffianDescent.SerreActualPointPulledSections
import PfaffianDescent.SerreTensorEvaluationPureWitnesses

/-! Actual section evaluation onto survives a genuine pullback, using
the literal pulled sections and native point composition isomorphism. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualPulledEvaluation_surjective
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F E] [Algebra L E]
    {X Y : Scheme.{u}} (base : X ⟶ Spec (.of F)) (base' : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (r : Fin 3 → (Spec (.of E) ⟶ Y))
    (q : Fin 3 → (Spec (.of E) ⟶ X))
    (hq : ∀ i, r i ≫ f = q i)
    (hr : ∀ i, r i ≫ base' = Spec.map (CommRingCat.ofHom (algebraMap L E)))
    (hqb : ∀ i, q i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (M : X.Modules)
    (honto : Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor base q hqb M)) :
    Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base' r hr ((Scheme.Modules.pullback f).obj M)) := by
  apply serreTensorEvaluation_surjective_of_pure_tensor_witnesses
    (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor base q hqb M)
    honto
    (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
      base' r hr ((Scheme.Modules.pullback f).obj M))
    (serreActualThreePointPulledGammaEquiv f r q hq M)
  intro s
  exact ⟨1 ⊗ₜ[L] serreActualPulledGlobalSection base base' f M s,
    serreActualThreePointPulledGammaEquiv_one_tmul base base' f r q hq hr hqb M s⟩

end PfaffianDescent

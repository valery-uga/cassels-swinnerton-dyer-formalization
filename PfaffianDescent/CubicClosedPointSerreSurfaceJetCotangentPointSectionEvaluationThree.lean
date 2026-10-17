import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationTensor

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Simultaneous E-linear evaluation of actual global sections at three
actual field-valued points, with the literal dependent native Gamma target. -/
def cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
    {F E : Type u} [Field F] [Field E] [Algebra F E] {X : Scheme.{u}}
    (base : X ⟶ Spec (CommRingCat.of F))
    (r : Fin 3 → (Spec (CommRingCat.of E) ⟶ X))
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (M : X.Modules) :
    E ⊗[F] SchemeModuleGlobalSectionsOver base M →ₗ[E]
      (∀ i : Fin 3, (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
        ((Scheme.Modules.pullback (r i)).obj M)) :=
  LinearMap.pi (fun i =>
    cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor base (r i) (hr i) M)

/-- The simultaneous actual point evaluator sends 1 tensor s to the SAME
literal three pulled-section values on the actual point spectra. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_one_tmul
    {F E : Type u} [Field F] [Field E] [Algebra F E] {X : Scheme.{u}}
    (base : X ⟶ Spec (CommRingCat.of F))
    (r : Fin 3 → (Spec (CommRingCat.of E) ⟶ X))
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    (M : X.Modules) (s : SchemeModuleGlobalSectionsOver base M) :
    cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor base r hr M
      (1 ⊗ₜ[F] s) = fun i =>
        (pullbackSection (r i) M (isIso_pullbackUnitComparison _) (M.unitHomEquiv s)).val (op ⊤) := by
  funext i
  exact cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor_one_tmul
    base (r i) (hr i) M s

/-- The literal simultaneous actual evaluation is natural for arbitrary
actual module maps, including the original actual Serre quotient map. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_naturality
    {F E : Type u} [Field F] [Field E] [Algebra F E] {X : Scheme.{u}}
    (base : X ⟶ Spec (CommRingCat.of F))
    (r : Fin 3 → (Spec (CommRingCat.of E) ⟶ X))
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap F E)))
    {M N : X.Modules} (π : M ⟶ N) (w : E ⊗[F] SchemeModuleGlobalSectionsOver base M) :
    (fun i => ((moduleSpecΓFunctor (R := CommRingCat.of E)).map
      ((Scheme.Modules.pullback (r i)).map π)).hom
        (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
          base r hr M w i)) =
    cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor base r hr N
      ((schemeModuleGlobalSectionsMap base π).baseChange E w) := by
  funext i
  exact cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluationTensor_naturality
    base (r i) (hr i) π w

end PfaffianDescent

import PfaffianDescent.CubicGroundKernelSerreGlobalJetLifts
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointSectionEvaluationThree

/-! The derivative map on the literal three native Serre point fibres.
Its values on actual global sections are the actual cubic-kernel jets. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist BundleSectionZeroLocus
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def cubicGroundKernelJetPoint
    {F E : Type u} [Field F] [Field E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (φ : Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E) :
    Spec (CommRingCat.of E) ⟶ Proj (grading I) :=
  Spec.map (CommRingCat.ofHom
    (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ)) ≫
      cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell

def cubicGroundKernelSerrePointDerivative
    {F L E : Type u} [Field F] [Field L] [Field E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (φ : Fin 3 → (Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E))
    (β : Fin 3 → (L →+* E))
    (hres : ∀ i, cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ i) = (β i).comp g)
    (M : (Proj (grading I)).Modules)
    (π : M ⟶ closedImmersionIdealTwist
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
      (positiveSheafOfModules (grading I) 3)) :
    (∀ i : Fin 3, (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback (cubicGroundKernelJetPoint I ell (φ i))).obj M)) →ₗ[E]
        (Fin 3 → Fin 2 → E) :=
  LinearMap.pi (fun i =>
    (cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernelPointFiberDerivative
      I ell g (φ i) (β i) (hres i)).comp
        ((((moduleSpecΓFunctor (R := CommRingCat.of E)).map
          ((Scheme.Modules.pullback (cubicGroundKernelJetPoint I ell (φ i))).map π)).hom).comp
            (LinearMap.proj i)))

theorem cubicGroundKernelSerrePointDerivative_pullback_apply
    {F L E : Type u} [Field F] [Field L] [Field E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (φ : Fin 3 → (Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E))
    (β : Fin 3 → (L →+* E))
    (hres : ∀ i, cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ i) = (β i).comp g)
    (M : (Proj (grading I)).Modules)
    (π : M ⟶ closedImmersionIdealTwist
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
      (positiveSheafOfModules (grading I) 3))
    (s : SheafOfModules.unit (Proj (grading I)).ringCatSheaf ⟶ M) (i : Fin 3) :
    cubicGroundKernelSerrePointDerivative I ell g φ β hres M π
      (fun k => (pullbackSection (cubicGroundKernelJetPoint I ell (φ k)) M
        (isIso_pullbackUnitComparison _) (M.unitHomEquiv s)).val (Opposite.op ⊤)) i =
    cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernelPointFiberDerivative
      I ell g (φ i) (β i) (hres i)
      ((SheafOfModules.sectionsMap
        ((Scheme.Modules.pullback (cubicGroundKernelJetPoint I ell (φ i))).map π)
          (pullbackSection (cubicGroundKernelJetPoint I ell (φ i)) M
            (isIso_pullbackUnitComparison _) (M.unitHomEquiv s))).val (Opposite.op ⊤)) := by
  rfl

end PfaffianDescent

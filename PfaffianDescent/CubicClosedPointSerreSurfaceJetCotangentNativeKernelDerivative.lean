import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelSections
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentTensor

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
variable {K A B : Type u} [Field K] [CommRing A] [CommRing B] [Algebra K A]
set_option backward.isDefEq.respectTransparency false

/-- A point of the ACTUAL closed subscheme internally puts its SAME H inside the
point maximal ideal. No independent H-containment certificate is required. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_nativeIdeal_le_pointIdeal
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) (g : A →+* B) (β : B →+* K)
    (hres : (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom = β.comp g) :
    RingHom.ker g ≤ cubicClosedPointSerreSurfaceJetCotangent_ideal φ := by
  intro a ha
  change g a = 0 at ha
  change (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom a = 0
  rw [hres]
  change β (g a) = 0
  rw [ha, map_zero]

/-- The canonical first derivative of the ACTUAL point-pulled-back original ideal,
using its native inclusion-compatible H coordinate and actual point factorization. -/
def cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberDerivative
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (β : B →+* K)
    (hres : (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom = β.comp g) :
    (moduleSpecΓFunctor (R := CommRingCat.of K)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom))).obj
        (IdealSheafDataModule.closedImmersionModule (Spec.map (CommRingCat.ofHom g)))) →ₗ[K]
      (Fin 2 → K) := by
  let r := (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom
  letI : Algebra A K := r.toAlgebra
  exact (cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative φ (RingHom.ker g)
      (cubicClosedPointSerreSurfaceJetCotangent_nativeIdeal_le_pointIdeal φ g β hres)).comp
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberSectionsEquiv g r).toLinearMap

/-- Exact actual ideal-section evaluation/first-derivative square, retaining SAME H. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberDerivative_evaluation
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (β : B →+* K)
    (hres : (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom = β.comp g)
    (a : RingHom.ker g) :
    cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberDerivative φ g β hres
      ((cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
        (CommRingCat.ofHom (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom)
        (IdealSheafDataModule.closedImmersionModule (Spec.map (CommRingCat.ofHom g)))).hom
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv g a)) =
    (φ a.1).snd := by
  let r := (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom
  letI : Algebra A K := r.toAlgebra
  change cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative φ (RingHom.ker g)
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdeal_le_pointIdeal φ g β hres)
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberSectionsEquiv g r _) = _
  rw [cubicClosedPointSerreSurfaceJetCotangent_nativeIdealPointEvaluation_apply,
    cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative_tmul, one_smul]

end PfaffianDescent

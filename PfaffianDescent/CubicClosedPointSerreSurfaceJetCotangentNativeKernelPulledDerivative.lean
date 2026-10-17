import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineEvaluationPullbackSection
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelSectionHom
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelRingDerivative

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
open IdealSheafDataModule BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual pulled affine ideal section has the original literal jet
derivative, even when chart and point fields differ. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_ringNativeIdealFiberDerivative_pulledSection
    {K A B : Type u} [Field K] [CommRing A] [CommRing B]
    (φ : A →+* CubicSurfaceFirstJet K)
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (β : B →+* K)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g)
    (h : RingHom.ker g) :
    cubicClosedPointSerreSurfaceJetCotangent_ringNativeIdealFiberDerivative φ g β hres
      ((pullbackSection
        (Spec.map (CommRingCat.ofHom (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ)))
        (closedImmersionModule (Spec.map (CommRingCat.ofHom g)))
        (isIso_pullbackUnitComparison _)
        ((closedImmersionModule (Spec.map (CommRingCat.ofHom g))).unitHomEquiv
          (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom g h))).val (op ⊤)) =
      (φ h.1).snd := by
  let N := closedImmersionModule (Spec.map (CommRingCat.ofHom g))
  let t := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom g h
  let r := cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ
  have ht : t.val.app (op ⊤) (1 : Γ(Spec (CommRingCat.of A), ⊤)) =
      cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv g h :=
    cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop_one N _
  have he := cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation_pullbackSection r N t
  have hn := congrArg (fun z =>
    (cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
      (CommRingCat.ofHom r) N).hom z) ht
  exact (congrArg
    (cubicClosedPointSerreSurfaceJetCotangent_ringNativeIdealFiberDerivative φ g β hres)
    (he.symm.trans hn)).trans
    (cubicClosedPointSerreSurfaceJetCotangent_ringNativeIdealFiberDerivative_evaluation φ g β hres h)

end PfaffianDescent

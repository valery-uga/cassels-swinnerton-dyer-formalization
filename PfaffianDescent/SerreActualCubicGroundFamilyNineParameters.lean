import PfaffianDescent.SerreActualCubicGroundFamilyProjections
import PfaffianDescent.SerreActualGroundKernelNineParameters

/-! The actual common cubic family retains the same kernel-plane parameters
in both nine-coordinate spaces. The new canonical basis and its rank are
derived from the original Serre bundle, rather than supplied independently. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable {N : (hypersurface p hp).Modules}
variable (e : SerreExtensionData (hypersurface p hp) N)
variable (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
variable [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
variable (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
variable (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
variable (hHG : H * G = 1)

@[reassoc]
theorem serreActualCubicGroundFamilyToOriginal_nineParameters :
    serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG ≫
      pullback.snd (hypersurfaceToBase p hp)
        (schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) e.E) ≫
      (serreIncidenceNineParameterIso (hypersurfaceToBase p hp) e.E h9).hom =
    pullback.snd
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        (toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F))) ≫
      serreKernelFrameProjectiveEmbedding G H hHG ≫
      projectiveFrameCoordinateCoefficientMap (m := 9) (algebraMap K F) := by
  rw [← Category.assoc, serreActualCubicGroundFamilyToOriginal_parameters,
    Category.assoc, serreActualGroundPlaneOriginalParameters_nine]

@[reassoc]
theorem serreActualCubicGroundKernelParameters_nine :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
    let baseF := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    let MF := (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
    let hn := (serreIncidenceCubicCoefficientGlobalSections_finrank (F := F) p hp e C).trans h9
    let b := serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9
    serreActualCubicGroundKernelParameters p hp e C h9 G H hHG ≫
      (serreIncidenceNineParameterIso baseF MF hn).hom =
    serreKernelFrameProjectiveEmbedding G H hHG ≫
      (projectiveBasisCoordinateIso b
        (finBasisOfFinrankEq F (SchemeModuleGlobalSectionsOver baseF MF) hn)).hom := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  exact serreActualGroundKernelCanonicalParameters_nine _ _ _ _ G H hHG

@[reassoc]
theorem serreActualCubicGroundFamilyToNew_nineParameters :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
    let baseF := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    let MF := (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
    let hn := (serreIncidenceCubicCoefficientGlobalSections_finrank (F := F) p hp e C).trans h9
    let b := serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9
    serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG ≫
      pullback.snd baseF (schemeModuleGlobalSectionsProjectiveParametersToBase baseF MF) ≫
      (serreIncidenceNineParameterIso baseF MF hn).hom =
    pullback.snd baseF
        (toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F))) ≫
      serreKernelFrameProjectiveEmbedding G H hHG ≫
      (projectiveBasisCoordinateIso b
        (finBasisOfFinrankEq F (SchemeModuleGlobalSectionsOver baseF MF) hn)).hom := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  dsimp only
  rw [← Category.assoc, serreActualCubicGroundFamilyToNew_parameters,
    Category.assoc, serreActualCubicGroundKernelParameters_nine]

end PfaffianDescent

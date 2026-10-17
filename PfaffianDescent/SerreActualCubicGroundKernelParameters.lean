import PfaffianDescent.SerreActualGroundKernelCanonicalParameters
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalFrame
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalDimension

/-! The same native ground kernel frame gives canonical section parameters
on the actual coefficient cubic. Its dimension and transported basis are
derived from the original Serre bundle. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
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

def serreActualCubicGroundKernelParameters
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
    scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F)) ⟶
      schemeModuleGlobalSectionsProjectiveParameters
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        ((Scheme.Modules.pullback
          (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  exact serreActualGroundKernelCanonicalParameters
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    ((Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E)
    ((serreIncidenceCubicCoefficientGlobalSections_finrank (F := F) p hp e C).trans h9)
    (serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9) G H hHG

@[reassoc]
theorem serreActualCubicGroundKernelParameters_toBase
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
    serreActualCubicGroundKernelParameters p hp e C h9 G H hHG ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        ((Scheme.Modules.pullback
          (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) =
      toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F)) := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  exact serreActualGroundKernelCanonicalParameters_toBase _ _ _ _ G H hHG

end PfaffianDescent

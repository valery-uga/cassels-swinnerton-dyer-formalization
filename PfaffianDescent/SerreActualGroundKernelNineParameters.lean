import PfaffianDescent.SerreActualGroundPlaneOriginalParameters
import PfaffianDescent.SerreActualGroundKernelCanonicalParameters

/-! The actual old and new parameter maps, in their actual nine-coordinate
projective spaces. This exposes the shared ground kernel frame and the
genuine canonical basis-change map used by the common family. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem serreActualGroundPlaneOriginalParameters_nine
    {K F : Type u} [Field K] [Field F] [Algebra K F] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) :
    serreActualGroundPlaneOriginalParameters base M h9 G H hHG ≫
      (serreIncidenceNineParameterIso base M h9).hom =
    serreKernelFrameProjectiveEmbedding G H hHG ≫
      projectiveFrameCoordinateCoefficientMap (m := 9) (algebraMap K F) := by
  simp only [serreActualGroundPlaneOriginalParameters,
    projectiveFrameCoordinateCoefficientMap, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

@[reassoc]
theorem serreActualGroundKernelCanonicalParameters_nine
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
    (b : Basis (Fin 9) K (SchemeModuleGlobalSectionsOver base M))
    (G : Matrix (Fin 9) (Fin 3) K) (H : Matrix (Fin 3) (Fin 9) K)
    (hHG : H * G = 1) :
    serreActualGroundKernelCanonicalParameters base M h9 b G H hHG ≫
      (serreIncidenceNineParameterIso base M h9).hom =
    serreKernelFrameProjectiveEmbedding G H hHG ≫
      (projectiveBasisCoordinateIso b
        (finBasisOfFinrankEq K (SchemeModuleGlobalSectionsOver base M) h9)).hom := by
  simp only [serreActualGroundKernelCanonicalParameters,
    serreActualProjectiveBasisParameterIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end PfaffianDescent

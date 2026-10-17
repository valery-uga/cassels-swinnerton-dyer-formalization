import PfaffianDescent.SerreActualGroundKernelCanonicalParameters
import AllCharacteristics.ProjectiveCoefficientMap

/-! The same ground kernel plane also maps to the original section
parameters through the literal coefficient projection. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreActualGroundPlaneOriginalParameters
    {K F : Type u} [Field K] [Field F] [Algebra K F] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) :
    scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F)) ⟶
      schemeModuleGlobalSectionsProjectiveParameters base M :=
  serreKernelFrameProjectiveEmbedding G H hHG ≫
    projectiveCoefficientMap (algebraMap K F)
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 9) K))
      (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 9) F)) (by simp) ≫
    (serreIncidenceNineParameterIso base M h9).inv

@[reassoc]
theorem serreActualGroundPlaneOriginalParameters_toBase
    {K F : Type u} [Field K] [Field F] [Algebra K F] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) :
    serreActualGroundPlaneOriginalParameters base M h9 G H hHG ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M =
      toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
  unfold serreActualGroundPlaneOriginalParameters
  rw [← serreIncidenceNineParameterIso_toBase base M h9]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [projectiveCoefficientMap_toBase, ← Category.assoc,
    serreKernelFrameProjectiveEmbedding_toBase]

end PfaffianDescent

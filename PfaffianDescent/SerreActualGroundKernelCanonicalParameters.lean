import PfaffianDescent.SerreActualProjectiveBasisParameter
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelProjectiveEmbedding

/-! The ground kernel plane maps into the actual canonical projective
section parameters, using the genuine transported-basis coordinate change.
The map is a closed immersion over the ground field. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreActualGroundKernelCanonicalParameters
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
    (b : Basis (Fin 9) K (SchemeModuleGlobalSectionsOver base M))
    (G : Matrix (Fin 9) (Fin 3) K) (H : Matrix (Fin 3) (Fin 9) K)
    (hHG : H * G = 1) :
    scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K)) ⟶
      schemeModuleGlobalSectionsProjectiveParameters base M :=
  serreKernelFrameProjectiveEmbedding G H hHG ≫
    (serreActualProjectiveBasisParameterIso base M h9 b).hom

instance serreActualGroundKernelCanonicalParameters_isClosedImmersion
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
    (b : Basis (Fin 9) K (SchemeModuleGlobalSectionsOver base M))
    (G : Matrix (Fin 9) (Fin 3) K) (H : Matrix (Fin 3) (Fin 9) K)
    (hHG : H * G = 1) :
    IsClosedImmersion (serreActualGroundKernelCanonicalParameters base M h9 b G H hHG) := by
  unfold serreActualGroundKernelCanonicalParameters
  infer_instance

@[reassoc]
theorem serreActualGroundKernelCanonicalParameters_toBase
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base M) = 9)
    (b : Basis (Fin 9) K (SchemeModuleGlobalSectionsOver base M))
    (G : Matrix (Fin 9) (Fin 3) K) (H : Matrix (Fin 3) (Fin 9) K)
    (hHG : H * G = 1) :
    serreActualGroundKernelCanonicalParameters base M h9 b G H hHG ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M =
      toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) K)) := by
  unfold serreActualGroundKernelCanonicalParameters
  rw [Category.assoc, serreActualProjectiveBasisParameterIso_toBase,
    serreKernelFrameProjectiveEmbedding_toBase]

end PfaffianDescent

import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelProjectiveEmbedding
import PfaffianDescent.SchemeAffineFunctions

/-! The actual ground-kernel parameter family has the same regular base
coefficient functions as its surface projection. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreActualGroundFamily_kernel_baseMap
    {F : Type u} [Field F] {X T : Scheme.{u}}
    (x : X ⟶ Spec (.of F))
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1)
    (t : T ⟶ pullback x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))) :
    affineFunctionHom (t ≫ pullback.snd x
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))) ≫
      serreKernelFrameProjectiveEmbedding G H hHG ≫
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F))) =
    affineFunctionHom (t ≫ pullback.fst x
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))) ≫ x) := by
  rw [serreKernelFrameProjectiveEmbedding_toBase]
  exact congrArg (fun g => affineFunctionHom (t ≫ g)) pullback.condition.symm

end PfaffianDescent

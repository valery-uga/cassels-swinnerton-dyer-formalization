import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelScheme
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProjectivePlane

/-! # The split kernel projective family is actually open over its affine base -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R]

theorem serreKernelEquationsSchemeIso_hom_toBase
    (A : Matrix (Fin 6) (Fin 9) R) (M : Matrix (Fin 9) (Fin 3) R)
    (N : Matrix (Fin 3) (Fin 9) R) (D : Matrix (Fin 9) (Fin 6) R)
    (hAM : A * M = 0) (hNM : N * M = 1) (hsplit : M * N + D * A = 1) :
    (serreKernelEquationsSchemeIso A M N D hAM hNM hsplit).hom ≫
      toBase (serreEvaluationHomogeneousIdeal A) =
        toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) := by
  change polynomialProjectiveMap (serreEvaluationHomogeneousIdeal A)
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R))
    (rectangularSubstitution M) (serreEvaluationEquationIdeal_le_ker A M hAM)
    (fun _ _ hp => rectangularSubstitution_homogeneous M hp)
    (rectangularSubstitution_surjective M N hNM) ≫ _ = _
  exact polynomialProjectiveMap_toBase _ _ _ _ _ _

/-- Actual split kernel equations give an open projective projection, via the
proved scheme isomorphism over the literal coefficient-ring spectrum. -/
theorem serreKernelEquationsToBase_isOpenMap
    (A : Matrix (Fin 6) (Fin 9) R) (M : Matrix (Fin 9) (Fin 3) R)
    (N : Matrix (Fin 3) (Fin 9) R) (D : Matrix (Fin 9) (Fin 6) R)
    (hAM : A * M = 0) (hNM : N * M = 1) (hsplit : M * N + D * A = 1) :
    IsOpenMap (toBase (serreEvaluationHomogeneousIdeal A)) := by
  let e := serreKernelEquationsSchemeIso A M N D hAM hNM hsplit
  have he : e.hom ≫ toBase (serreEvaluationHomogeneousIdeal A) =
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) :=
    serreKernelEquationsSchemeIso_hom_toBase A M N D hAM hNM hsplit
  have hπ : e.inv ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) =
      toBase (serreEvaluationHomogeneousIdeal A) := by
    rw [← he]
    simp
  letI : Smooth (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R))) :=
    smooth_toBase_bot
  rw [← hπ]
  exact (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R))).isOpenMap.comp
    e.inv.isOpenMap

end PfaffianDescent

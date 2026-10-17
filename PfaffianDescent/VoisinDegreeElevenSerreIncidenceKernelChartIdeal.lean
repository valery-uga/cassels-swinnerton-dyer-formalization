import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelChartEquations
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIdealCover

/-! # Actual kernel Proj immersion restricted to each actual affine chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreEvaluationKernel_projective_chart_ideal
    {R : Type u} [CommRing R] (A : Matrix (Fin 6) (Fin 9) R) (j : Fin 9) :
    (schemeQuotientMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R))
      (serreEvaluationHomogeneousIdeal A) bot_le).ker.comap
        (chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R)) j) =
    (Spec.map (CommRingCat.ofHom (chartQuotientMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R))
      (serreEvaluationHomogeneousIdeal A) bot_le j))).ker := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R) := ⊥
  let J := serreEvaluationHomogeneousIdeal A
  let c := schemeQuotientMap I J bot_le
  letI : IsClosedImmersion c := schemeQuotientMap_closedImmersion I J bot_le
  have h := isPullback_schemeQuotientMap_chart I J bot_le j
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion c (chartι I j),
    ← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end PfaffianDescent

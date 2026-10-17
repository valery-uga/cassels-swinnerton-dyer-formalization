import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelScheme
import PfaffianDescent.QuotientChartKernel

/-! # Literal normalized chart equations of the actual homogeneous kernel Proj -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreEvaluationKernel_chart_ker
    {R : Type u} [CommRing R] (A : Matrix (Fin 6) (Fin 9) R) (j : Fin 9) :
    RingHom.ker (chartQuotientMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R))
      (serreEvaluationHomogeneousIdeal A) bot_le j) =
    Ideal.span (Set.range fun r : Fin 6 => ∑ k : Fin 9,
      chartBaseMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R)) j (A r k) *
      chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R)) j k) := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R) := ⊥
  let ev := MvPolynomial.eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  have he : (chartPresentationIdeal I j).map ev = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker ev).mpr
    rw [chartEvaluation_ker]
  have hp : chartPresentationIdeal (serreEvaluationHomogeneousIdeal A) j =
      chartPresentationIdeal I j ⊔ serreEvaluationEquationIdeal A := by
    simp only [chartPresentationIdeal, I, HomogeneousIdeal.toIdeal_bot,
      serreEvaluationHomogeneousIdeal, bot_sup_eq]
    exact sup_comm _ _
  rw [chartQuotientMap_ker_eq_presentationImage, hp, Ideal.map_sup,
    he, bot_sup_eq, serreEvaluationEquationIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext r
  simp [ev, rectangularLinearCoordinate, Matrix.mulVec, dotProduct]

end PfaffianDescent

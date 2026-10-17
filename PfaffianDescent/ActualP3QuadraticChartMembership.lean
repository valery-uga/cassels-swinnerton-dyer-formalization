import PfaffianDescent.IntrinsicFullQuadraticSystem

/-! SOURCE ONLY / UNVERIFIED. Literal scheme-section restriction criterion
for the existing intrinsic four-chart submodule, including nilpotents. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem mem_intrinsicFullQuadraticSystem_iff_chart_restrictions_zero
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [QuasiCompact i]
    (p : MvPolynomial (Fin 4) K) :
    p ∈ intrinsicFullQuadraticSystem i ↔
      p.IsHomogeneous 2 ∧ ∀ j : Fin 4,
        i.app (intrinsicQuadraticAmbientOpen (K := K) j).1
          ((Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)).hom
            (ambientChartEvaluation j p)) = 0 := by
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro j
    have hj := (Submodule.mem_iInf _).mp hp.2 j
    let U := intrinsicQuadraticAmbientOpen (K := K) j
    change (Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)).hom
      (ambientChartEvaluation j p) ∈ i.ker.ideal U at hj
    rw [i.ker_apply U] at hj
    change i.app U.1
      ((Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)).hom
        (ambientChartEvaluation j p)) = 0 at hj
    exact hj
  · rintro ⟨hp, hz⟩
    refine ⟨hp, (Submodule.mem_iInf _).mpr ?_⟩
    intro j
    let U := intrinsicQuadraticAmbientOpen (K := K) j
    change (Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)).hom
      (ambientChartEvaluation j p) ∈ i.ker.ideal U
    rw [i.ker_apply U]
    change i.app U.1
      ((Proj.awayToSection (homogeneousSubmodule (Fin 4) K) (X j)).hom
        (ambientChartEvaluation j p)) = 0
    exact hz j

end PfaffianDescent

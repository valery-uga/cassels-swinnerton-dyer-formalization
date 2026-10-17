import PfaffianDescent.P3CanonicalTraceOriginalBaseLinear187
import PfaffianDescent.CorayCubicLinearPairH1RankOne

/-! Exact six existing trace187 stages. Packaging split only. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
local notation "P" => Proj PS
local notation "piP" => ambientToBase (R := K) (σ := Fin 4)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Bounded ambient stage: the SAME two Cartier boundaries followed by
its SAME Laurent-normalized P3 trace. No intrinsic action conversion occurs
in this declaration, and only one linear-map composition is checked. -/
def cubicLinearPairBoundaryTrace187
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    [HasExt.{u} (P).Modules] :
    letI : Linear K (P).Modules := schemeModulesLinearOver piP
    schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p l hp 1 hl) 0))) 1 →ₗ[K] K := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  have hnot := nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0
  exact (p3NegativeFourCohomologyThreeTraceLinearEquiv187 K).toLinearMap.comp
    (cubicSecondEquation_twoBoundaryLinearMap p l hp hp0 1 hl hnot)

/-- A one-composition value cut; the actual boundary and trace are opaque
in all subsequent conversion checks. -/
theorem cubicLinearPairBoundaryTrace_apply187
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    [HasExt.{u} (P).Modules] :
    let hnot := nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0
    ∀ z : schemeModuleCohomology P
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (cokernel (mulHomogeneous (grading (equationIdeal p hp))
          (cubicSecondEquationHomogeneous p l hp 1 hl) 0))) 1,
      cubicLinearPairBoundaryTrace187 p l hp hp0 hl hl0 z =
        p3NegativeFourCohomologyThreeTraceEquiv K
          (cubicSecondEquation_twoBoundaryLinearMap p l hp hp0 1 hl hnot z) := by
  dsimp only
  intro z
  rfl

/-- Actual degree-one boundary surjectivity and the canonical trace
surjectivity, checked without the coefficient or closed-pushforward layers. -/
theorem cubicLinearPairBoundaryTrace_surjective187
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    [HasExt.{u} (P).Modules] :
    Function.Surjective (cubicLinearPairBoundaryTrace187 p l hp hp0 hl hl0) := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  have hnot := nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0
  exact (p3NegativeFourCohomologyThreeTraceLinearEquiv187 K).surjective.comp
    (cubicSecondEquation_twoBoundaryLinearMap_surjective_degree_one
      p l hp hp0 hl hnot)

/-- Bounded coefficient stage: the actual unit-pushforward coefficient
isomorphism, followed by the preceding actual ambient stage. -/
def cubicLinearPairPushforwardTrace187
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    [HasExt.{u} (P).Modules] :
    let I := projectiveIntersectionIdeal p l hp hl
    let X := scheme I
    letI : Linear K (P).Modules := schemeModulesLinearOver piP
    schemeModuleCohomology P
      ((Scheme.Modules.pushforward (quotientProjMap I)).obj
        (SheafOfModules.unit X.ringCatSheaf)) 1 →ₗ[K] K := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  have hnot := nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0
  exact (cubicLinearPairBoundaryTrace187 p l hp hp0 hl hl0).comp
    (cubicSecondEquation_zeroCokernelAmbientCohomologyOneLinearEquiv
      p l hp hp0 1 hl hnot).symm.toLinearMap

/-- Keep the coefficient inverse explicit on each actual class while
unfolding only this single composition. -/
theorem cubicLinearPairPushforwardTrace_apply187
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    [HasExt.{u} (P).Modules] :
    let I := projectiveIntersectionIdeal p l hp hl
    let X := scheme I
    let hnot := nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0
    ∀ z : schemeModuleCohomology P
      ((Scheme.Modules.pushforward (quotientProjMap I)).obj
        (SheafOfModules.unit X.ringCatSheaf)) 1,
      cubicLinearPairPushforwardTrace187 p l hp hp0 hl hl0 z =
        cubicLinearPairBoundaryTrace187 p l hp hp0 hl hl0
          ((cubicSecondEquation_zeroCokernelAmbientCohomologyOneLinearEquiv
            p l hp hp0 1 hl hnot).symm z) := by
  dsimp only
  intro z
  rfl

/-- Genuine coefficient-inverse surjectivity is composed only with the
already checked bounded ambient-stage surjectivity. -/
theorem cubicLinearPairPushforwardTrace_surjective187
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    [HasExt.{u} (P).Modules] :
    Function.Surjective (cubicLinearPairPushforwardTrace187 p l hp hp0 hl hl0) := by
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  have hnot := nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0
  exact (cubicLinearPairBoundaryTrace_surjective187 p l hp hp0 hl hl0).comp
    (cubicSecondEquation_zeroCokernelAmbientCohomologyOneLinearEquiv
      p l hp hp0 1 hl hnot).symm.surjective

end PfaffianDescent.Coray

import PfaffianDescent.CorayCubicLinearPairTraceStages187
import PfaffianDescent.ClosedImmersionH1OriginalBaseMap187

/-! Exact three original trace187 endpoints importing the unchanged stages. -/
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

def cubicLinearPairAmbientTrace187
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    [HasExt.{u} (scheme (projectiveIntersectionIdeal p l hp hl)).Modules]
    [HasExt.{u} (P).Modules] :
    let I := projectiveIntersectionIdeal p l hp hl
    let X := scheme I
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
    schemeModuleCohomology X (SheafOfModules.unit X.ringCatSheaf) 1 →ₗ[K] K := by
  let I := projectiveIntersectionIdeal p l hp hl
  let X := scheme I
  letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  exact (cubicLinearPairPushforwardTrace187 p l hp hp0 hl hl0).comp
    (closedImmersion_cohomologyOneLinearMapOver187 (toBase I) piP
      (quotientProjMap I) (quotientProjMap_toBase I)
      (SheafOfModules.unit X.ringCatSheaf))

theorem cubicLinearPairAmbientTrace_apply187
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    [HasExt.{u} (scheme (projectiveIntersectionIdeal p l hp hl)).Modules]
    [HasExt.{u} (P).Modules] :
    let I := projectiveIntersectionIdeal p l hp hl
    let X := scheme I
    let hnot := nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0
    ∀ z : schemeModuleCohomology X (SheafOfModules.unit X.ringCatSheaf) 1,
      cubicLinearPairAmbientTrace187 p l hp hp0 hl hl0 z =
        p3NegativeFourCohomologyThreeTraceEquiv K
          (cubicSecondEquation_twoBoundaryLinearMap p l hp hp0 1 hl hnot
            ((cubicSecondEquation_zeroCokernelAmbientCohomologyOneLinearEquiv
              p l hp hp0 1 hl hnot).symm
                (closedImmersion_cohomologyOneLinearMap piP (quotientProjMap I)
                  (SheafOfModules.unit X.ringCatSheaf) z))) := by
  dsimp only
  intro z
  simp only [cubicLinearPairAmbientTrace187, LinearMap.comp_apply,
    cubicLinearPairPushforwardTrace_apply187,
    cubicLinearPairBoundaryTrace_apply187,
    closedImmersion_cohomologyOneLinearMapOver_apply187]

theorem cubicLinearPairAmbientTrace_surjective187
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    [HasExt.{u} (scheme (projectiveIntersectionIdeal p l hp hl)).Modules]
    [HasExt.{u} (P).Modules] :
    Function.Surjective (cubicLinearPairAmbientTrace187 p l hp hp0 hl hl0) := by
  let I := projectiveIntersectionIdeal p l hp hl
  let X := scheme I
  letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
  letI : Linear K (P).Modules := schemeModulesLinearOver piP
  exact (cubicLinearPairPushforwardTrace_surjective187 p l hp hp0 hl hl0).comp
    (closedImmersion_cohomologyOneLinearMapOver_surjective187 (toBase I) piP
      (quotientProjMap I) (quotientProjMap_toBase I)
      (SheafOfModules.unit X.ringCatSheaf))

end PfaffianDescent.Coray

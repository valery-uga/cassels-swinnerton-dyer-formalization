import PfaffianDescent.CorayCubicSecondEquationBoundarySurjective
import PfaffianDescent.ClosedImmersionCohomologyOneLinearEquiv
import PfaffianDescent.CorayActualGenericPlaneSectionH1Bound
import PfaffianDescent.P3CanonicalCohomologyTrace
import Mathlib.LinearAlgebra.Dimension.Finite

/-! SOURCE ONLY / UNVERIFIED161. Actual original-field H1 rank1 for the
entire cubic/linear pair. Nontriviality is derived from the actual intrinsic
comparison, coefficient isomorphism, two boundaries and native P3 trace.
Finite H1 and its original-field upper bound are prior actual producers. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native intrinsic H1 of the entire pair is nonzero. This is a genuine
construction through existing actual maps, not a genus/equality premise. -/
theorem smoothCubicLinearPair_unit_cohomology_one_nontrivial
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    [HasExt.{u} (scheme (projectiveIntersectionIdeal p l hp hl)).Modules]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules] :
    Nontrivial (schemeModuleCohomology (scheme (projectiveIntersectionIdeal p l hp hl))
      (SheafOfModules.unit (scheme (projectiveIntersectionIdeal p l hp hl)).ringCatSheaf) 1) := by
  let I := projectiveIntersectionIdeal p l hp hl
  let X := scheme I
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  let piP := ambientToBase (R := K) (σ := Fin 4)
  letI : Linear K P.Modules := schemeModulesLinearOver piP
  letI : Linear K X.Modules := schemeModulesLinearOver (quotientProjMap I ≫ piP)
  have hnot := nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0
  let eCoeff := cubicSecondEquation_zeroCokernelAmbientCohomologyOneLinearEquiv
    p l hp hp0 1 hl hnot
  let f := (cubicSecondEquation_twoBoundaryLinearMap p l hp hp0 1 hl hnot).comp
    (eCoeff.symm.toLinearMap.comp
      (closedImmersion_cohomologyOneLinearMap piP (quotientProjMap I)
        (SheafOfModules.unit X.ringCatSheaf)))
  have hf : Function.Surjective f :=
    (cubicSecondEquation_twoBoundaryLinearMap_surjective_degree_one
        p l hp hp0 hl hnot).comp
      (eCoeff.symm.surjective.comp
        (closedImmersion_cohomologyOneLinearMap_surjective piP (quotientProjMap I)
          (SheafOfModules.unit X.ringCatSheaf)))
  have hTrace : Function.Surjective
      (fun z => p3NegativeFourCohomologyThreeTraceEquiv K (f z)) :=
    (p3NegativeFourCohomologyThreeTraceEquiv K).surjective.comp hf
  exact hTrace.nontrivial

/-- Entire smooth-cubic/linear pair H1 is finite with original-K rank
EXACTLY one, from independently produced upper bound and nontriviality. -/
theorem smoothCubicLinearPair_unit_cohomology_one_finite_finrank_eq_one
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0) :
    let I := projectiveIntersectionIdeal p l hp hl
    let X := scheme I
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
    Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) ∧
      Module.finrank K (schemeModuleCohomology X
        (SheafOfModules.unit X.ringCatSheaf) 1) = 1 := by
  let I := projectiveIntersectionIdeal p l hp hl
  let X := scheme I
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives P.Modules := sheafOfModules_enoughInjectives P.ringCatSheaf
  letI : HasExt.{u} P.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} P.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver (toBase I)
  have hBound := smoothCubicLinearPair_unit_cohomology_one_finite_finrank_le_one
    p l hp hp0 hl hl0
  letI : Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) := hBound.1
  letI : Nontrivial (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) :=
    smoothCubicLinearPair_unit_cohomology_one_nontrivial p l hp hp0 hl hl0
  have hPos : 0 < Module.finrank K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) := Module.finrank_pos
  exact ⟨hBound.1, Nat.le_antisymm hBound.2 (Nat.succ_le_of_lt hPos)⟩

end PfaffianDescent.Coray

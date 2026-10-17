import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationMap
import PfaffianDescent.SerreExtensionFoundation
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Actual pullback projection at a canonical zero is an isomorphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Pullback carries the actual Serre cokernel to a cokernel. If the literal
canonical inclusion pulls back to zero, its literal quotient map is an iso. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_pullback_projection_isIso
    {X Z : Scheme.{u}} {M : X.Modules}
    (e : SerreExtensionSequenceData X M) (j : Z ⟶ X)
    (hzero : (Scheme.Modules.pullback j).map e.inclusion = 0) :
    IsIso ((Scheme.Modules.pullback j).map e.projection) := by
  let P := Scheme.Modules.pullback j
  letI : P.PreservesZeroMorphisms := inferInstanceAs
    ((Scheme.Modules.pullback j).PreservesZeroMorphisms)
  letI : PreservesColimits P := inferInstanceAs
    (PreservesColimits (Scheme.Modules.pullback j))
  have hcol : IsColimit (CokernelCofork.ofπ (P.map e.projection)
      (by rw [← P.map_comp, e.zero, P.map_zero])) :=
    CokernelCofork.mapIsColimit _ e.shortExact.gIsCokernel P
  exact CokernelCofork.IsColimit.isIso_π _ hcol hzero

/-- The actual section evaluation being zero supplies the cokernel theorem's
zero map, using the canonical invertible unit comparison. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_pullback_projection_isIso_of_evaluation_zero
    {K : Type u} [Field K] {X Z : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionSequenceData X M) (j : Z ⟶ X)
    (hzero : cubicClosedPointSerreDegreeThreeEvaluationMap base j
      (show X.Modules from e.E) e.inclusion = 0) :
    IsIso ((Scheme.Modules.pullback j).map e.projection) := by
  apply cubicClosedPointSerreDegreeThreeEvaluation_pullback_projection_isIso e j
  letI : IsIso (pullbackUnitComparison j) := isIso_pullbackUnitComparison j
  let u := asIso (pullbackUnitComparison j)
  change u.inv ≫ (Scheme.Modules.pullback j).map e.inclusion = 0 at hzero
  apply (cancel_epi u.inv).mp
  simpa only [comp_zero] using hzero

/-- On actual global sections of the pullback, the literal Serre quotient
map is a ground-field-linear equivalence whenever the canonical section
vanishes. This works for arbitrary scheme maps, including split components. -/
def cubicClosedPointSerreDegreeThreeEvaluation_pullback_firstDerivativeEquiv
    {K : Type u} [Field K] {X Z : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionSequenceData X M) (j : Z ⟶ X)
    (hzero : cubicClosedPointSerreDegreeThreeEvaluationMap base j
      (show X.Modules from e.E) e.inclusion = 0) :
    SchemeModuleGlobalSectionsOver (j ≫ base)
      ((Scheme.Modules.pullback j).obj (show X.Modules from e.E)) ≃ₗ[K]
    SchemeModuleGlobalSectionsOver (j ≫ base) ((Scheme.Modules.pullback j).obj M) := by
  let q := (Scheme.Modules.pullback j).map e.projection
  letI : IsIso q :=
    cubicClosedPointSerreDegreeThreeEvaluation_pullback_projection_isIso_of_evaluation_zero
      base e j hzero
  exact
    { schemeModuleGlobalSectionsMap (j ≫ base) q with
      invFun := fun s => s ≫ inv q
      left_inv := by intro s; change (s ≫ q) ≫ inv q = s; simp
      right_inv := by intro s; change (s ≫ inv q) ≫ q = s; simp }

/-- The equivalence is literally composition with the pulled projection. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_pullback_firstDerivativeEquiv_apply
    {K : Type u} [Field K] {X Z : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionSequenceData X M) (j : Z ⟶ X)
    (hzero : cubicClosedPointSerreDegreeThreeEvaluationMap base j
      (show X.Modules from e.E) e.inclusion = 0)
    (s : SchemeModuleGlobalSectionsOver (j ≫ base)
      ((Scheme.Modules.pullback j).obj (show X.Modules from e.E))) :
    cubicClosedPointSerreDegreeThreeEvaluation_pullback_firstDerivativeEquiv base e j hzero s =
      s ≫ (Scheme.Modules.pullback j).map e.projection := rfl

/-- Actual section evaluation commutes with the original Serre projection
and the native first-derivative equivalence. -/
theorem cubicClosedPointSerreDegreeThreeEvaluation_pullback_firstDerivativeEquiv_evaluation
    {K : Type u} [Field K] {X Z : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionSequenceData X M) (j : Z ⟶ X)
    (hzero : cubicClosedPointSerreDegreeThreeEvaluationMap base j
      (show X.Modules from e.E) e.inclusion = 0)
    (s : SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) :
    cubicClosedPointSerreDegreeThreeEvaluation_pullback_firstDerivativeEquiv base e j hzero
      (cubicClosedPointSerreDegreeThreeEvaluationMap base j (show X.Modules from e.E) s) =
    cubicClosedPointSerreDegreeThreeEvaluationMap base j M
      (schemeModuleGlobalSectionsMap base e.projection s) := by
  letI : IsIso (pullbackUnitComparison j) := isIso_pullbackUnitComparison j
  change (inv (pullbackUnitComparison j) ≫ (Scheme.Modules.pullback j).map s) ≫
    (Scheme.Modules.pullback j).map e.projection =
      inv (pullbackUnitComparison j) ≫ (Scheme.Modules.pullback j).map (s ≫ e.projection)
  rw [Functor.map_comp, Category.assoc]

end PfaffianDescent

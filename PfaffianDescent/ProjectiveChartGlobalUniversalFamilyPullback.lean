import PfaffianDescent.ProjectiveChartGlobalUniversalWholeFamily
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic

/-! Literal original197 pullback of the CONSTRUCTED whole global
universal family. Actual all-test naturality and original chart recovery
are derived; forward classification and final NatIso remain separate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v w
set_option autoImplicit false

/-- Bounded abstract Type-functor application law before any concrete
scheme/family carrier is substituted. Explicit types_comp_apply normalizes
the ordinary concrete-category composite application. -/
private theorem globalUniversalPullback_TypeFunctor_comp_apply001
    {C : Type v} [Category.{w} C] (A : Cᵒᵖ ⥤ Type u)
    {T W V : C} (g : T ⟶ W) (t : W ⟶ V) (P : A.obj (.op V)) :
    A.map (g ≫ t).op P = A.map g.op (A.map t.op P) := by
  simpa only [op_comp, types_comp_apply] using
    ConcreteCategory.congr_hom (A.map_comp t.op g.op) P

variable {J : Type u} {X B : Scheme.{u}} (F : X ⟶ B) (U : J → X.Opens) (n : ℕ)
variable [IsSeparated F] (H : J → Over B)
variable (eta : ∀ i, relativeFiniteFlatHilbertFunctor197 ((U i).ι ≫ F) n ≅ yoneda.obj (H i))

/-- The inverse candidate on EVERY original-base scheme test is the
literal native197 pullback of the constructed global universal family.
No test family, global ideal or inverse outcome is supplied as a premise. -/
def relativeOpenChartParameterGlobalUniversalFamilyPullback001
    (T : Over B) (g : T ⟶ relativeOpenChartParameterGluedObject001 F U n H eta) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n :=
  (relativeFiniteFlatHilbertFunctor197 F n).map g.op
    (relativeOpenChartParameterGlobalUniversalFamily001 F U n H eta)

/-- The complete original ideal is exactly the native comap of the
constructed global WHOLE ideal, retaining every nilpotent. -/
theorem relativeOpenChartParameterGlobalUniversalFamilyPullback_wholeIdeal001
    (T : Over B) (g : T ⟶ relativeOpenChartParameterGluedObject001 F U n H eta) :
    (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T g).val =
      (relativeOpenChartParameterGlobalUniversalWholeIdeal001 F U n H eta).comap
        (relativeHilbertAmbientMap197 F g) := rfl

/-- Actual all-test naturality, proved by the bounded abstract functor
law on the literal original197 pullback maps. -/
theorem relativeOpenChartParameterGlobalUniversalFamilyPullback_natural001
    {T0 T1 : Over B} (a : T0 ⟶ T1)
    (g : T1 ⟶ relativeOpenChartParameterGluedObject001 F U n H eta) :
    relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T0 (a ≫ g) =
      (relativeFiniteFlatHilbertFunctor197 F n).map a.op
        (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T1 g) :=
  globalUniversalPullback_TypeFunctor_comp_apply001
    (relativeFiniteFlatHilbertFunctor197 F n) a g
    (relativeOpenChartParameterGlobalUniversalFamily001 F U n H eta)

/-- On every test into an original parameter chart, pullback recovers
EXACTLY its own classified whole ambient point. Recovery uses the
constructed global family's exact chart restriction, not a matching input. -/
theorem relativeOpenChartParameterGlobalUniversalFamilyPullback_chartRecovery001
    (i : J) (T : Over B) (g : T ⟶ H i) :
    relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T
      (g ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i) =
      relativeOpenChartClassifiedAmbientPoint001 F (U i) n (H i) (eta i) T g := by
  have hComposition :
      (relativeFiniteFlatHilbertFunctor197 F n).map
        (g ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).op
        (relativeOpenChartParameterGlobalUniversalFamily001 F U n H eta) =
      (relativeFiniteFlatHilbertFunctor197 F n).map g.op
        ((relativeFiniteFlatHilbertFunctor197 F n).map
          (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).op
          (relativeOpenChartParameterGlobalUniversalFamily001 F U n H eta)) :=
    globalUniversalPullback_TypeFunctor_comp_apply001
      (relativeFiniteFlatHilbertFunctor197 F n) g
      (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)
      (relativeOpenChartParameterGlobalUniversalFamily001 F U n H eta)
  have hMapped :
      (relativeFiniteFlatHilbertFunctor197 F n).map g.op
        ((relativeFiniteFlatHilbertFunctor197 F n).map
          (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).op
          (relativeOpenChartParameterGlobalUniversalFamily001 F U n H eta)) =
      (relativeFiniteFlatHilbertFunctor197 F n).map g.op
        (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i)) :=
    congrArg (fun Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F (H i)) n =>
      (relativeFiniteFlatHilbertFunctor197 F n).map g.op Q)
      (relativeOpenChartParameterGlobalUniversalFamily_chart001 F U n H eta i)
  exact hComposition.trans (hMapped.trans
    (relativeOpenChartClassifiedAmbientPoint_eq_pullback001 F (U i) n (H i) (eta i) T g).symm)

/-- Genuine inverse-side natural transformation from the SAME glued
parameter object, constructed by Yoneda from its actual global universal
family. No representability or natural-isomorphism conclusion is assumed. -/
def relativeOpenChartParameterGlobalUniversalFamilyPullbackNatTrans001 :
    yoneda.obj (relativeOpenChartParameterGluedObject001 F U n H eta) ⟶
      relativeFiniteFlatHilbertFunctor197 F n :=
  yonedaEquiv.symm (relativeOpenChartParameterGlobalUniversalFamily001 F U n H eta)

/-- The actual transformation component is precisely the literal
native197 pullback candidate on arbitrary original scheme tests. -/
theorem relativeOpenChartParameterGlobalUniversalFamilyPullbackNatTrans_app001
    (T : Over B) (g : T ⟶ relativeOpenChartParameterGluedObject001 F U n H eta) :
    (relativeOpenChartParameterGlobalUniversalFamilyPullbackNatTrans001 F U n H eta).app (.op T) g =
      relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T g := rfl

end PfaffianDescent
end

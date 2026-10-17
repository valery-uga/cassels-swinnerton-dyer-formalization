import PfaffianDescent.OriginalPlaneFirstCartierStalkComparison196
import PfaffianDescent.SchemeIsoPushforwardUnit
import PfaffianDescent.SchemePushforwardUnitSections
import PfaffianDescent.SchemeModuleInternalHomSupportedFiberIso

/-! Actual coordinates for the SAME original curve embedded in the plane
section through a genuine scheme Iso. No supported class is substituted. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open SchemeModuleInternalHom IdealSheafDataModule
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual original source-unit pushforward to the SAME original plane
cokernel. The intermediate source coordinate is the existing native scheme
Iso pushforward-unit comparison, never an assumed quotient comparison. -/
def originalCurveSurfaceUnitCokernelIso210
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl)) :
    (Scheme.Modules.pushforward
      (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl)).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      (homogeneousRestrictionSequence (grading (equationIdeal p hp))
        (cubicSecondEquationHomogeneous p l hp 1 hl) 0).X₃ :=
  ((Scheme.Modules.pushforwardComp e.hom
      (cubicSecondEquationCurveImmersion p l hp 1 hl)).app
        (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
    (Scheme.Modules.pushforward (cubicSecondEquationCurveImmersion p l hp 1 hl)).mapIso
      (schemeIsoPushforwardUnitIso e) ≪≫
    (cubicSecondEquation_zeroCokernelIsoCurveUnit p l hp hp0 1 hl
      (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0)).symm

/-- The canonical surface point ideal-sequence target is identified with
the pushforward of the SAME whole original curve point-dual quotient. -/
def originalCurvePointSurfaceSupportedSourceIso210
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hl : l.IsHomogeneous 1)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl))
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (E : (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃ ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) :
    (closedImmersionIdealTwistSequence
      (i ≫ (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl))
        (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃ ≅
      (Scheme.Modules.pushforward
        (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl)).obj
          (incrementCokernelSequence (closedImmersionModuleToUnit i)).X₃ :=
  closedImmersionIdealTwistSequenceUnitTargetIso
    (i ≫ (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl)) ≪≫
    ((Scheme.Modules.pushforwardComp i
      (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl)).app
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).symm ≪≫
    (Scheme.Modules.pushforward
      (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl)).mapIso E.symm

end PfaffianDescent.Coray

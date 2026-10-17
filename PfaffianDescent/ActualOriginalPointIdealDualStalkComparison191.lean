import PfaffianDescent.SchemeModuleActualOverNativeStalkChart191
import PfaffianDescent.SchemeModuleActualDualOverEvaluation191
import PfaffianDescent.CorayPerfectOwnNormalizationPointIdealRankOne
import Mathlib.LinearAlgebra.Dual.Defs

/-! Source-only191. Native original-ring dual-stalk comparison from the
ACTUAL original ideal chart. The dual chart evaluates actual sections on
that same frame. The canonical increment and whole evaluation maps are
preserved, rather than supplied as comparison premises. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SchemeModuleInternalHom
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The WHOLE actual canonical evaluation has precisely the actual native
tensor-chart stalk map. This square precedes the point/trace assembly and
contains no evaluation-compatibility certificate premise. -/
theorem actualDualEvaluation_nativeStalk_chart191
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).map (dualEvaluation M) =
      (actualOverNativeStalkChartIso191 U x
        (schemeModuleTensorOverUnitIso M (dual M) U e (dualOverUnitIso U e))).hom :=
  (actualOverNativeStalkChartIso_hom_of_global191 U x
    (schemeModuleTensorOverUnitIso M (dual M) U e (dualOverUnitIso U e))
    (dualEvaluation M) (actualDualEvaluation_over_eq_tensorChart191 M U e)).symm

/-- Actual original-frame coordinate on native stalks. Its inverse is the
native stalk map of the ORIGINAL chart inverse, followed by the unit frame. -/
def originalIdealFrameNativeStalkIso191
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (U.ι x)) (X.presheaf.stalk (U.ι x)) :=
  (actualOverNativeStalkChartIso191 U x e.symm).symm ≪≫
    schemeModuleUnitStalkIso X (U.ι x)

/-- The ACTUAL dual coefficient is carried through the native stalk chart.
It is the existing section-evaluation map, not a chosen stalk functional. -/
def actualDualFrameNativeStalkIso191
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj (dual M) ≅
      ModuleCat.of (X.presheaf.stalk (U.ι x)) (X.presheaf.stalk (U.ι x)) :=
  actualOverNativeStalkChartIso191 U x (dualOverUnitIso U e) ≪≫
    schemeModuleUnitStalkIso X (U.ι x)

/-- Actual dual-sheaf stalk identified with the linear dual of the SAME
original module stalk, using the independently original local-ring actions. -/
def actualDualNativeStalkLinearEquiv191
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj (dual M) ≃ₗ[X.presheaf.stalk (U.ι x)]
      Module.Dual (X.presheaf.stalk (U.ι x))
        ((schemeModuleStalkModuleFunctor X (U.ι x)).obj M) :=
  (actualDualFrameNativeStalkIso191 U x M e).toLinearEquiv.trans
    ((LinearMap.ringLmapEquivSelf (X.presheaf.stalk (U.ι x))
      (X.presheaf.stalk (U.ι x)) (X.presheaf.stalk (U.ι x))).symm.trans
        (originalIdealFrameNativeStalkIso191 U x M e).toLinearEquiv.dualMap)

/-- Actual frame/product evaluation of the constructed native comparison. -/
theorem actualDualNativeStalkLinearEquiv_apply191
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (a : (schemeModuleStalkModuleFunctor X (U.ι x)).obj (dual M))
    (m : (schemeModuleStalkModuleFunctor X (U.ι x)).obj M) :
    actualDualNativeStalkLinearEquiv191 U x M e a m =
      (originalIdealFrameNativeStalkIso191 U x M e).toLinearEquiv m *
        (actualDualFrameNativeStalkIso191 U x M e).toLinearEquiv a := rfl

/-- In the SAME original frame, the comparison returns the actual
stalk coefficient of literal section evaluation on that frame. -/
theorem actualDualNativeStalkLinearEquiv_frame191
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (a : (schemeModuleStalkModuleFunctor X (U.ι x)).obj (dual M)) :
    actualDualNativeStalkLinearEquiv191 U x M e a
        ((originalIdealFrameNativeStalkIso191 U x M e).toLinearEquiv.symm 1) =
      (actualDualFrameNativeStalkIso191 U x M e).toLinearEquiv a := by
  rw [actualDualNativeStalkLinearEquiv_apply191,
    LinearEquiv.apply_symm_apply, one_mul]

/-- The actual canonical unitToHom map becomes r times the ORIGINAL
inclusion functional on native stalks. The true over-site square is
proved previously from original section evaluation and is transported here. -/
theorem actualDualNativeStalkLinearEquiv_unitToHom191
    (U : X.Opens) (x : U) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (j : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (r : X.presheaf.stalk (U.ι x)) :
    actualDualNativeStalkLinearEquiv191 U x M e
        ((schemeModuleStalkModuleFunctor X (U.ι x)).map (unitToHom j)
          ((schemeModuleUnitStalkIso X (U.ι x)).inv r)) =
      r • (((schemeModuleStalkModuleFunctor X (U.ι x)).map j ≫
        (schemeModuleUnitStalkIso X (U.ι x)).hom).hom) := by
  let R := X.presheaf.stalk (U.ι x)
  let F := schemeModuleStalkModuleFunctor X (U.ι x)
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let u := schemeModuleUnitStalkIso X (U.ι x)
  let qM := (originalIdealFrameNativeStalkIso191 U x M e).toLinearEquiv
  let qD := (actualDualFrameNativeStalkIso191 U x M e).toLinearEquiv
  let jR : F.obj M →ₗ[R] R := (F.map j ≫ u.hom).hom
  have hs := actualOverNativeStalkChartIso_square191 U x e.symm
    (dualOverUnitIso U e) (unitToHom j) j (unitToHom_overCoefficient j U e)
  have hd : qD (F.map (unitToHom j) (u.inv r)) = jR (qM.symm r) := by
    have hv := congrArg (fun k : F.obj O ⟶ F.obj O => u.hom (k (u.inv r))) hs
    exact hv
  apply LinearMap.ext
  intro m
  calc
    _ = qM m * qD (F.map (unitToHom j) (u.inv r)) :=
      actualDualNativeStalkLinearEquiv_apply191 U x M e _ m
    _ = qM m * jR (qM.symm r) := congrArg (fun z : R => qM m * z) hd
    _ = jR (qM m • qM.symm r) := (jR.map_smul (qM m) (qM.symm r)).symm
    _ = jR (r • m) := by
      apply congrArg jR
      apply qM.injective
      rw [qM.map_smul, qM.apply_symm_apply, qM.map_smul]
      exact mul_comm _ _
    _ = _ := jR.map_smul r m

namespace Coray
open IdealSheafDataModule

/-- Literal ORIGINAL I_P caller. Actual regular/DVR geometry spreads its
original ideal frame internally. The resulting dual-stalk equivalence keeps
both the WHOLE original evaluation and the SAME original increment map.
No frame, dual comparison or map-square conclusion is a premise. -/
theorem closedPointIdeal_exists_actualDualStalkComparison191
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := dual M
    let F := schemeModuleStalkModuleFunctor X P.1
    ∃ (U : X.Opens) (hPU : P.1 ∈ U)
      (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U),
      let c := actualDualNativeStalkLinearEquiv191 U ⟨P.1, hPU⟩ M e
      F.map (dualEvaluation M) =
          (actualOverNativeStalkChartIso191 U ⟨P.1, hPU⟩
            (schemeModuleTensorOverUnitIso M D U e (dualOverUnitIso U e))).hom ∧
        ∀ r : X.presheaf.stalk P.1,
          c (F.map (unitToHom (closedImmersionModuleToUnit i))
            ((schemeModuleUnitStalkIso X P.1).inv r)) =
          r • ((F.map (closedImmersionModuleToUnit i) ≫
            (schemeModuleUnitStalkIso X P.1).hom).hom) := by
  classical
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  have hM := closedPointIdeal_locallyRankOne_of_stalk_isDVR X P
  obtain ⟨U, hPU, ⟨e⟩⟩ := hM P.1
  refine ⟨U, hPU, e, ?_, ?_⟩
  · exact actualDualEvaluation_nativeStalk_chart191 U ⟨P.1, hPU⟩ M e
  · intro r
    exact actualDualNativeStalkLinearEquiv_unitToHom191 U ⟨P.1, hPU⟩ M e
      (closedImmersionModuleToUnit i) r

end Coray
end PfaffianDescent

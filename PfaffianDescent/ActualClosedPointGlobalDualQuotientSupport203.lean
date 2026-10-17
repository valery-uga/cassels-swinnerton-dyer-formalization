import PfaffianDescent.SchemeModuleInternalHomSupportedFiberIso
import PfaffianDescent.ActualClosedPointWholeDualCokernelPrincipal194
import Mathlib.AlgebraicGeometry.FunctionField

/-! SOURCE ONLY203. The WHOLE global canonical point-dual quotient of the
SAME original curve is the actual residue-point pushforward. Genuine ideal
charts construct the intrinsic fiber frame and retain the original projection. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open SchemeModuleInternalHom IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original point geometry constructs both the true intrinsic fiber frame
and the WHOLE global quotient identification, with its actual projection.
The target is the actual original residue-point sheaf; no support/fiber/quotient
comparison or normalization premise is supplied. -/
theorem actualClosedPoint_exists_globalDualQuotientSupport203
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := dual M
    let S := incrementCokernelSequence (closedImmersionModuleToUnit i)
    S.ShortExact ∧
    ∃ b : (Scheme.Modules.pullback i).obj D ≅
        (show (Spec (X.residueField P.1)).Modules from
          SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf),
      ∃ E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
          (show (Spec (X.residueField P.1)).Modules from
            SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf),
        S.g ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
          (Scheme.Modules.pushforward i).map b.hom := by
  classical
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  have hS := actualClosedPointDualIncrement_shortExact194 X P
  refine ⟨hS, ?_⟩
  have hM : schemeModuleLocallyRankOne M := Coray.closedPointIdeal_locallyRankOne_of_stalk_isDVR X P
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts M hM
  let U := B P.1
  have hrange : Set.range i ⊆ Set.range U.ι := by
    rintro x ⟨z, rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact ⟨⟨P.1, hB P.1⟩, rfl⟩
  let j := IsOpenImmersion.lift U.ι i hrange
  have hji : j ≫ U.ι = i := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (j ≫ U.ι) := hji.symm ▸ inferInstance
  let eB' (x : X) : (closedImmersionModule (j ≫ U.ι)).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x) := by
    rw [hji]
    exact eB x
  let D := dual (closedImmersionModule (j ≫ U.ι))
  let S := incrementCokernelSequence (closedImmersionModuleToUnit (j ≫ U.ι))
  let b := schemeModuleFiberFrameIso U.ι j D (dualRestrictUnitIso U (eB' P.1))
  let c := closedImmersionDualIncrement_canonicalFiberIso U j B hB eB' (eB' P.1)
  let E := c ≪≫ (Scheme.Modules.pushforward (j ≫ U.ι)).mapIso b
  have hresult : ∃ b : (Scheme.Modules.pullback (j ≫ U.ι)).obj D ≅
      (show (Spec (X.residueField P.1)).Modules from
        SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf),
    ∃ E : S.X₃ ≅ (Scheme.Modules.pushforward (j ≫ U.ι)).obj
      (show (Spec (X.residueField P.1)).Modules from
        SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf),
      S.g ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app D ≫
        (Scheme.Modules.pushforward (j ≫ U.ι)).map b.hom := by
    refine ⟨b, E, ?_⟩
    change cokernel.π (unitToHom (closedImmersionModuleToUnit (j ≫ U.ι))) ≫
      (c.hom ≫ (Scheme.Modules.pushforward (j ≫ U.ι)).map b.hom) = _
    rw [← Category.assoc, closedImmersionDualIncrement_canonicalFiberIso_projection]
  let supportPredicate (k : Spec (X.residueField P.1) ⟶ X) : Prop :=
    let Dk := dual (closedImmersionModule k)
    let Sk := incrementCokernelSequence (closedImmersionModuleToUnit k)
    ∃ b : (Scheme.Modules.pullback k).obj Dk ≅
        (show (Spec (X.residueField P.1)).Modules from
          SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf),
      ∃ E : Sk.X₃ ≅ (Scheme.Modules.pushforward k).obj
          (show (Spec (X.residueField P.1)).Modules from
            SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf),
        Sk.g ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app Dk ≫
          (Scheme.Modules.pushforward k).map b.hom
  have hlocal : supportPredicate (j ≫ U.ι) := hresult
  exact Eq.mp (congrArg supportPredicate hji) hlocal

end PfaffianDescent

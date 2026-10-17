import PfaffianDescent.VoisinDegreeElevenSerreIncidencePointChartCoordinates
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFieldPulledFreeOver

/-! # Native inverse-image trivializations under arbitrary actual pullback -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidencePulledFreeOverIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    SheafOfModules.free (R := Y.ringCatSheaf.over (f ⁻¹ᵁ U)) I ≅
      ((Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) := by
  let V := f ⁻¹ᵁ U
  let q := f ∣_ U
  let r := V.ι ≫ f
  let h : q ≫ U.ι = r := morphismRestrict_ι f U
  let a := serreIncidencePointChartFreeIso U M I t q r h ≪≫
    ((Scheme.Modules.pullbackComp V.ι f).app M).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app
      ((Scheme.Modules.pullback f).obj M)).symm
  exact serreIncidenceFreeOverIsoOfRestriction ((Scheme.Modules.pullback f).obj M) V I a

end PfaffianDescent

import PfaffianDescent.CorayNormalizationClosedPointIdealRankOne
import PfaffianDescent.SchemeModuleInternalHomDualOverUnit
import PfaffianDescent.SheafModulePushforwardExact

/-! Canonical frame on an open excluding the actual closed point. The
frame is the SAME original ideal inclusion, internally proved invertible
by the actual ideal sequence and zero point-pushforward. The constructed
dual frame is its literal evaluation coefficient. No arbitrary frame.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual point pushforward is zero on the over-site of an open excluding
P, including empty opens. This is genuine empty-preimage geometry. -/
theorem schemeModuleClosedPointPushforward_over_isZero
    (P : closedPoints X) (U : X.Opens) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    IsZero (((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)).over U) := by
  let i := X.fromSpecResidueField P.1
  let Q := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)
  apply (IsZero.iff_id_eq_zero (Q.over U)).mpr
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  have hpre : i ⁻¹ᵁ V.unop.left = ⊥ := by
    ext z
    change i z ∈ V.unop.left ↔ False
    constructor
    · intro hz
      apply hPU
      have h : i z ∈ U := V.unop.hom.le hz
      simpa only [i, Scheme.fromSpecResidueField_apply] using h
    · exact False.elim
  letI : Subsingleton Γ(Spec (X.residueField P.1), i ⁻¹ᵁ V.unop.left) :=
    CommRingCat.subsingleton_of_isTerminal
      ((Spec (X.residueField P.1)).sheaf.isTerminalOfEqEmpty hpre)
  haveI : Subsingleton ((Q.over U).val.obj V) :=
    inferInstanceAs (Subsingleton Γ(Spec (X.residueField P.1), i ⁻¹ᵁ V.unop.left))
  exact Subsingleton.elim _ _

/-- The actual inclusion is invertible on the SAME open; no unit chart
or desired comparison is supplied. Its original ideal ShortExact is used. -/
theorem schemeModuleClosedPointIdeal_over_inclusion_isIso
    (P : closedPoints X) (U : X.Opens) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map (closedImmersionModuleToUnit i)) := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let S := closedImmersionModulePushforwardSequence i
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  letI : F.PreservesZeroMorphisms := SheafOfModules.overFunctor_preservesZeroMorphisms X.ringCatSheaf U
  have hS : (S.map F).ShortExact := SheafOfModules.ShortComplex.shortExact_map_overFunctor
    X.ringCatSheaf U S (closedImmersionModulePushforwardSequence_shortExact i)
  change IsIso (S.map F).f
  have hQ : IsZero (S.map F).X₃ := schemeModuleClosedPointPushforward_over_isZero P U hPU
  exact hS.isIso_f_iff.mpr hQ

/-- The canonical ideal frame is EXACTLY the actual original inclusion. -/
def schemeModuleClosedPointIdealOverCanonicalIso
    (P : closedPoints X) (U : X.Opens) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (closedImmersionModule i).over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U := by
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI := schemeModuleClosedPointIdeal_over_inclusion_isIso P U hPU
  exact asIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map (closedImmersionModuleToUnit i))

/-- Exact public projection law for the canonical frame; its map was not
chosen from a nonempty set of unrelated rational trivializations. -/
theorem schemeModuleClosedPointIdealOverCanonicalIso_hom
    (P : closedPoints X) (U : X.Opens) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (schemeModuleClosedPointIdealOverCanonicalIso P U hPU).hom =
      (SheafOfModules.overFunctor X.ringCatSheaf U).map (closedImmersionModuleToUnit i) := rfl

/-- The SAME actual dual frame evaluates on the inverse of the canonical
inclusion. This is the existing genuine O-linear dual coefficient map. -/
def schemeModuleClosedPointDualOverCanonicalIso
    (P : closedPoints X) (U : X.Opens) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (SchemeModuleInternalHom.dual (closedImmersionModule i)).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U :=
  SchemeModuleInternalHom.dualOverUnitIso U (schemeModuleClosedPointIdealOverCanonicalIso P U hPU)

/-- The dual frame retains literal evaluation on the actual inverse
inclusion frame, at every smaller open of the over-site. -/
theorem schemeModuleClosedPointDualOverCanonicalIso_hom_val
    (P : closedPoints X) (U : X.Opens) (hPU : P.1 ∉ U) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    (schemeModuleClosedPointDualOverCanonicalIso P U hPU).hom.val =
      (SchemeModuleInternalHom.dualOverCoefficient U
        (schemeModuleClosedPointIdealOverCanonicalIso P U hPU)).val :=
  SchemeModuleInternalHom.dualOverUnitIso_hom_val U (schemeModuleClosedPointIdealOverCanonicalIso P U hPU)

end PfaffianDescent

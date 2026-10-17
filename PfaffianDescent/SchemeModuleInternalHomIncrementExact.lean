import PfaffianDescent.SchemeModuleInternalHomIncrementCoefficient
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Topology.Sheaves.Sheaf

/-! Genuine GLOBAL monicity of the SAME canonical increment and its
literal categorical cokernel short exact sequence. Target separation
and actual chart restrictions derive monicity. The quotient is NOT yet
identified here with a point pushforward/pullback fiber.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {M : X.Modules}

/-- GLOBAL section injectivity is derived from the original source
sheaf separation and actual pointwise unit charts. No injective-section,
regularity, inverse or point-increment certificate is an input. -/
theorem unitToHom_app_injective_of_pointwise_unitCharts
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j]
    (U : X → X.Opens) (hU : ∀ x, x ∈ U x)
    (e : ∀ x, M.over (U x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (U x))
    (W : X.Opens) : Function.Injective ((unitToHom j).val.app (op W)) := by
  intro r s hrs
  apply TopCat.Presheaf.IsSheaf.section_ext
    (F := (SheafOfModules.unit X.ringCatSheaf).val.presheaf)
    (SheafOfModules.unit X.ringCatSheaf).isSheaf
  intro x hxW
  let V : X.Opens := W ⊓ U x
  let f : V ⟶ W := homOfLE inf_le_left
  let g : V ⟶ U x := homOfLE inf_le_right
  let eV := overUnitChartRestrict M g (e x)
  refine ⟨V, inf_le_left, ⟨hxW, hU x⟩, ?_⟩
  apply unitToHom_app_injective j V eV
  calc
    _ = (dual M).val.map f.op ((unitToHom j).val.app (op W) r) :=
      PresheafOfModules.naturality_apply (unitToHom j).val f.op r
    _ = (dual M).val.map f.op ((unitToHom j).val.app (op W) s) :=
      congrArg ((dual M).val.map f.op) hrs
    _ = _ := (PresheafOfModules.naturality_apply (unitToHom j).val f.op s).symm

/-- GLOBAL monicity of the canonical SAME-inclusion increment. The only
generic chart hypotheses are internally discharged by primitive callers. -/
theorem unitToHom_mono_of_pointwise_unitCharts
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j]
    (U : X → X.Opens) (hU : ∀ x, x ∈ U x)
    (e : ∀ x, M.over (U x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (U x)) :
    Mono (unitToHom j) := by
  haveI : Mono (unitToHom j).val := PresheafOfModules.mono_of_injective
    (fun {W} => unitToHom_app_injective_of_pointwise_unitCharts j U hU e W.unop)
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map (by
    change Mono (unitToHom j).val
    infer_instance)

/-- The genuine increment sequence uses the SAME canonical map and the
literal categorical cokernel projection. No residue quotient is renamed. -/
abbrev incrementCokernelSequence (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    ShortComplex X.Modules := ShortComplex.cokernelSequence (unitToHom j)

/-- Genuine short exactness follows from INTERNALLY derived monicity,
with the actual canonical cokernel/projection and no exactness premise. -/
theorem incrementCokernelSequence_shortExact_of_pointwise_unitCharts
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j]
    (U : X → X.Opens) (hU : ∀ x, x ∈ U x)
    (e : ∀ x, M.over (U x) ≅ (SheafOfModules.unit X.ringCatSheaf).over (U x)) :
    (incrementCokernelSequence j).ShortExact where
  exact := ShortComplex.cokernelSequence_exact (unitToHom j)
  mono_f := by
    change Mono (unitToHom j)
    exact unitToHom_mono_of_pointwise_unitCharts j U hU e
  epi_g := by
    change Epi (cokernel.π (unitToHom j))
    infer_instance

end PfaffianDescent.SchemeModuleInternalHom

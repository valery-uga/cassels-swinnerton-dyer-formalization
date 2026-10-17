import PfaffianDescent.SchemeModuleFixedFrameStalkFieldImageOnChart
import PfaffianDescent.SchemeModuleClosedPointCanonicalFrameRestriction
import PfaffianDescent.SchemeModuleClosedPointGenericFunctionField

/-! Off-center negative AND positive point factors have the full native
local-ring field image under the SAME fixed-complement map. Actual point
complement charts and proved shrinking derive the result; no image or
rank-one certificate is input. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem le_pointComplement (P : closedPoints X) (C : X.Opens) (hPC : P.1 ∉ C) :
    C ≤ schemeClosedPointComplementOpen P := by
  intro y hy
  change y ≠ P.1
  intro he
  exact hPC (he ▸ hy)

/-- The actual negative point-factor stalk at EVERY x different from P
injects into the original function field with exactly the native local-ring
image, even when x is excluded from the word's smaller common complement. -/
theorem schemeModuleClosedPointIdealFixedComplementStalkToFunctionField_offCenter
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (C : X.Opens) [Nonempty C] (hPC : P.1 ∉ C) (x : X) (hxP : x ≠ P.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    letI := schemeModuleStalkModule M x
    let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
      (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) x
    Function.Injective ψ ∧ Set.range ψ =
      Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  letI := schemeModuleStalkModule M x
  let B := schemeClosedPointComplementOpen P
  have hxB : x ∈ B := hxP
  letI : Nonempty B := ⟨⟨x, hxB⟩⟩
  let f : C ⟶ B := homOfLE (le_pointComplement P C hPC)
  let eB := schemeModuleClosedPointIdealOverCanonicalIso P B (schemeClosedPoint_not_mem_complement P)
  have hC : SchemeModuleInternalHom.overUnitChartRestrict M f eB =
      schemeModuleClosedPointIdealOverCanonicalIso P C hPC :=
    schemeModuleClosedPointIdealOverCanonicalIso_restrict P f (schemeClosedPoint_not_mem_complement P)
  have hψ : schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
      (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) x =
      schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M B eB x :=
    (congrArg (fun e => schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x) hC).symm.trans
      (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_shrink pi M B C f eB x)
  rw [hψ]
  exact ⟨schemeModuleFixedFrameStalkToFunctionFieldLinearMap_injective_of_mem pi M B eB x hxB,
    schemeModuleFixedFrameStalkToFunctionFieldLinearMap_range_of_mem pi M B eB x hxB⟩

/-- The SAME actual positive dual-factor stalk has the native local-ring
field image and genuine injectivity at EVERY off-center point. The dual
unit chart comes from actual evaluation on the original inverse inclusion,
not an assumed rank-one, frame compatibility or field-image condition. -/
theorem schemeModuleClosedPointDualFixedComplementStalkToFunctionField_offCenter
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (C : X.Opens) [Nonempty C] (hPC : P.1 ∉ C) (x : X) (hxP : x ≠ P.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
    letI := schemeModuleStalkModule D x
    let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi D C
      (schemeModuleClosedPointDualOverCanonicalIso P C hPC) x
    Function.Injective ψ ∧ Set.range ψ =
      Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (closedImmersionModule i)
  letI := schemeModuleStalkModule D x
  let B := schemeClosedPointComplementOpen P
  have hxB : x ∈ B := hxP
  letI : Nonempty B := ⟨⟨x, hxB⟩⟩
  let f : C ⟶ B := homOfLE (le_pointComplement P C hPC)
  let eB := schemeModuleClosedPointDualOverCanonicalIso P B (schemeClosedPoint_not_mem_complement P)
  have hC : SchemeModuleInternalHom.overUnitChartRestrict D f eB =
      schemeModuleClosedPointDualOverCanonicalIso P C hPC :=
    schemeModuleClosedPointDualOverCanonicalIso_restrict P f (schemeClosedPoint_not_mem_complement P)
  have hψ : schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi D C
      (schemeModuleClosedPointDualOverCanonicalIso P C hPC) x =
      schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi D B eB x :=
    (congrArg (fun e => schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi D C e x) hC).symm.trans
      (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_shrink pi D B C f eB x)
  rw [hψ]
  exact ⟨schemeModuleFixedFrameStalkToFunctionFieldLinearMap_injective_of_mem pi D B eB x hxB,
    schemeModuleFixedFrameStalkToFunctionFieldLinearMap_range_of_mem pi D B eB x hxB⟩

end PfaffianDescent
